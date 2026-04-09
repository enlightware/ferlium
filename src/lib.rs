// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use derive_new::new;
pub use rustc_hash::{FxHashMap, FxHashSet};

use ::std::mem;
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
mod type_constraints;
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
pub use module::Path;
pub use type_inference::SubOrSameType;

use type_scheme::DisplayStyle;
pub use ustr::{Ustr, ustr};

use crate::{
    ast::PExprArena,
    containers::b,
    emit_ir::EmitModuleFrom,
    format::FormatWith,
    module::{
        Module, ModuleFunction, ModuleId, Uses,
        id::{Id, NamedIndexed},
    },
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

/// All data needed to rebuild the module.
#[derive(Clone, Debug, new)]
pub struct ModuleSrcInfo {
    /// The source code used
    source_id: SourceId,
    /// The use directive used
    uses: Uses,
}

/// A module that has been attempted to be compiled at least once.
#[derive(Debug)]
pub struct ModuleEntry {
    /// Informations needed to rebuild the module, if it supports rebuilding (std doesn't).
    src_info: Option<ModuleSrcInfo>,
    /// Last good compiled module (without stale deps at that time).
    /// Must be not-None if [`stale`] is false.
    module: Option<Module>,
    /// Compilation error, if last compilation failed.
    last_error: Option<CompilationError>,
    /// Deps from latest successful self build, stale or not.
    latest_deps: Vec<ModuleId>,
    /// Whether this module or some of its dependencies failed to compile.
    stale: bool,
}

impl ModuleEntry {
    /// New fresh module that cannot be rebuilt (e.g. std).
    pub fn new_fresh_raw(module: Module) -> Self {
        let deps = module.deps().collect();
        ModuleEntry {
            src_info: None,
            module: Some(module),
            last_error: None,
            latest_deps: deps,
            stale: false,
        }
    }

    /// New fresh module that can be rebuilt later.
    pub fn new_fresh(src_info: ModuleSrcInfo, module: Module) -> Self {
        let deps = module.deps().collect();
        ModuleEntry {
            src_info: Some(src_info),
            module: Some(module),
            last_error: None,
            latest_deps: deps,
            stale: false,
        }
    }

    /// New module that compiled but whose dependencies are stale, and can be rebuilt later.
    pub fn new_stale(src_info: ModuleSrcInfo, deps: Vec<ModuleId>) -> Self {
        ModuleEntry {
            src_info: Some(src_info),
            module: None,
            last_error: None,
            latest_deps: deps,
            stale: true,
        }
    }

    /// New module that failed to compile but can be rebuilt later.
    pub fn new_with_error(src_info: ModuleSrcInfo, error: CompilationError) -> Self {
        ModuleEntry {
            src_info: Some(src_info),
            module: None,
            last_error: Some(error),
            latest_deps: vec![],
            stale: true,
        }
    }

    /// Our module compiled successfully, but some of its dependencies are stale.
    pub fn update_with_stale(
        &mut self,
        src_info: ModuleSrcInfo,
        old_module: Option<Module>,
        latest_deps: Vec<ModuleId>,
    ) {
        self.src_info = Some(src_info);
        self.module = old_module;
        self.last_error = None;
        self.latest_deps = latest_deps;
        self.stale = true;
    }

    /// Our module failed to compile, but can be rebuilt later.
    pub fn update_with_compilation_error(
        &mut self,
        src_info: ModuleSrcInfo,
        old_module: Option<Module>,
        error: CompilationError,
    ) {
        self.src_info = Some(src_info);
        self.module = old_module;
        self.last_error = Some(error);
        self.stale = true;
    }

    pub fn module(&self) -> Option<&Module> {
        self.module.as_ref()
    }

    pub fn is_stale(&self) -> bool {
        self.stale
    }
}

/// A set of modules indexed both by name (Path) and by numeric ID (ModuleId).
/// This is the canonical way to hold a collection of modules in a compilation session.
pub type Modules = NamedIndexed<Path, ModuleId, ModuleEntry>;

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
        modules.insert(std_name, ModuleEntry::new_fresh_raw(std_module));
        let empty_std_user = new_module_using_std(modules.next_id());
        let empty_std_user = modules.insert(
            module::Path::single_str("$empty_std_user"),
            ModuleEntry::new_fresh_raw(empty_std_user),
        );
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
    pub fn get_module_entry_by_id(&self, id: ModuleId) -> Option<&ModuleEntry> {
        self.modules.get(id)
    }

    /// Get a module environment, with an empty module including the standard library
    /// for debugging purposes.
    pub fn module_env(&self) -> ModuleEnv<'_> {
        ModuleEnv {
            modules: &self.modules,
            current: self.expect_fresh_module(self.empty_std_user),
        }
    }

    /// Get the standard library module.
    pub fn std_module(&self) -> &Module {
        self.expect_fresh_module(STD_MODULE_ID)
    }

    /// Reset the compiler session to its initial state, without rebuilding std.
    pub fn reset(&mut self) {
        // We only keep std and $empty_std_user and drop the rest.
        self.modules.truncate(FIRST_USER_MODULE_ID.as_index());
        self.source_table.truncate(self.initial_source_table_size);
    }

    /// Register a module without Ferlium source in this compilation session and return its id.
    pub fn register_module(&mut self, path: module::Path, module: Module) -> ModuleId {
        let module_id = self
            .modules
            .insert(path, ModuleEntry::new_fresh_raw(module));
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
            let entry = self.modules.get(output.module_id).unwrap();
            if let Some(module) = &entry.module {
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
        // Add the source to the table first so every failure path can reference it.
        let source_id = self
            .source_table
            .add_source(source_name.to_string(), src_code.to_string());

        compile_with_source_id(
            source_id,
            &self.source_table,
            &mut self.modules,
            ModuleRef::ByPath(module_path),
            uses,
            ast_inspector,
        )
    }

    /// Returns the entry for module_id, or panic if not found.
    pub fn expect_module_entry(&self, module_id: ModuleId) -> &ModuleEntry {
        self.modules()
            .get(module_id)
            .unwrap_or_else(|| panic!("Module {module_id} not found"))
    }

    /// Returns a fresh module for module_id, or panic if none is available.
    pub fn expect_fresh_module(&self, module_id: ModuleId) -> &Module {
        let entry = self.expect_module_entry(module_id);
        if entry.stale {
            panic!("Module {module_id} is stale due to failed compilation, cannot access it");
        }
        entry.module().unwrap()
    }

    /// Returned the last good compiled module for module_id, or panic if none exists.
    pub fn expect_compiled_module(&self, module_id: ModuleId) -> &Module {
        let entry = self.expect_module_entry(module_id);
        entry
            .module
            .as_ref()
            .unwrap_or_else(|| panic!("Module {module_id} does not have a compiled version"))
    }

    /// Run a function from a module, given its path and name, through a user-provided runner.
    pub fn run_fn<R>(
        &self,
        module_id: ModuleId,
        name: &str,
        runner: impl FnOnce(&ModuleFunction, &Module, &Modules) -> Result<R, String>,
    ) -> Result<R, String> {
        let entry = self
            .modules()
            .get(module_id)
            .ok_or_else(|| format!("Module {module_id} not found"))?;
        if entry.stale {
            return Err(format!(
                "Module {module_id} is stale due to failed compilation, cannot run function {name}"
            ));
        }
        let module = entry.module().unwrap();
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

/// Identifies the module being compiled, allowing the caller to either supply
/// a [`Path`] (for a module that may or may not already exist) or a known
/// [`ModuleId`] (for cascade recompilations where the module is guaranteed to
/// exist). Using [`ModuleRef::Existing`] skips the name-lookup and avoids any
/// [`Path`] clone.
enum ModuleRef {
    /// Look the module up by path; insert a new entry if it does not yet exist.
    ByPath(Path),
    /// The module is known to already exist at this ID; skip the name lookup.
    Existing(ModuleId),
}

impl ModuleRef {
    pub fn into_path(self) -> Option<Path> {
        match self {
            ModuleRef::ByPath(path) => Some(path),
            ModuleRef::Existing(_) => None,
        }
    }
}

/// Core compilation function, called once the source text has already been
/// registered in the [`SourceTable`]. Accepts a [`SourceId`] instead of raw
/// source strings so that cascade recompilations can skip the duplicate
/// [`SourceTable::add_source`] call and the associated string clones.
fn compile_with_source_id(
    source_id: SourceId,
    source_table: &SourceTable,
    modules: &mut Modules,
    module_ref: ModuleRef,
    uses: Uses,
    ast_inspector: Option<AstInspectorCb<'_>>,
) -> Result<ModuleAndExpr, CompilationError> {
    // Retrieve the source text registered under this id.
    let src_code = source_table
        .get_source_text(source_id)
        .expect("source_id must point to a valid entry in the source table");

    // Locate (or prepare to create) the module entry and temporarily replace
    // its compiled module with a dummy so the new compilation cannot see the
    // old version of itself.
    let next_module_id = modules.next_id();
    let (module_id, old_module) = match &module_ref {
        ModuleRef::ByPath(path) => {
            if let Some((id, entry)) = modules.get_mut_by_name(path) {
                let old = entry
                    .module
                    .as_mut()
                    .map(|m| mem::replace(m, Module::new(next_module_id)));
                (id, old)
            } else {
                (next_module_id, None)
            }
        }
        ModuleRef::Existing(id) => {
            let id = *id;
            let old = modules.get_mut(id).and_then(|e| {
                e.module
                    .as_mut()
                    .map(|m| mem::replace(m, Module::new(next_module_id)))
            });
            (id, old)
        }
    };
    let src_info = ModuleSrcInfo::new(source_id, uses.clone());

    // Closure called on every compilation failure, to restore the old module and mark dependencies.
    let process_compilation_failed =
        |modules: &mut Modules,
         path_for_new: Option<Path>,
         src_info: ModuleSrcInfo,
         old_module: Option<Module>,
         error: &CompilationError| {
            let error = error.clone();
            if let Some(entry) = modules.get_mut(module_id) {
                entry.update_with_compilation_error(src_info, old_module, error);
                mark_stale_transitively(modules, module_id)
            } else if let Some(path) = path_for_new {
                modules.insert(path, ModuleEntry::new_with_error(src_info, error));
            } else {
                panic!("Existing module not found — should never happen.");
            }
        };

    // Parse the source code.
    let (module_ast, expr_ast, arena) = match parse_module_and_expr(src_code, source_id, false) {
        Ok(result) => result,
        Err(error) => {
            let error = compilation_error!(ParsingFailed(error));
            let path_for_new = module_ref.into_path();
            process_compilation_failed(modules, path_for_new, src_info, old_module, &error);
            return Err(error);
        }
    };
    if let Some(ast_inspector) = ast_inspector {
        ast_inspector(&module_ast, expr_ast, &arena, modules);
    }

    // Emit IR for the module.
    let emit_from = EmitModuleFrom::Uses(uses);
    let mut module = match emit_module(module_ast, &arena, module_id, modules, emit_from) {
        Ok(result) => result,
        Err(error) => {
            // Resolve types in the error, to provide better error messages.
            let module = new_module_using_std(module_id);
            let env = ModuleEnv::new(&module, modules);
            let error = CompilationError::resolve_types(error, &env, source_table);
            let path_for_new = module_ref.into_path();
            process_compilation_failed(modules, path_for_new, src_info, old_module, &error);
            return Err(error);
        }
    };

    // Emit IR for the expression, if any.
    let expr = if let Some(expr_ast) = expr_ast {
        let compiled_expr = match emit_expr(expr_ast, &arena, &mut module, modules, vec![]) {
            Ok(result) => result,
            Err(error) => {
                // Resolve types in the error, to provide better error messages.
                let env = ModuleEnv::new(&module, modules);
                let error = CompilationError::resolve_types(error, &env, source_table);
                let path_for_new = module_ref.into_path();
                process_compilation_failed(modules, path_for_new, src_info, old_module, &error);
                return Err(error);
            }
        };
        Some(compiled_expr)
    } else {
        None
    };

    // Detect cycles in the module dependency graph.
    if let Some(cycle) = find_module_deps_cycle(modules, module_id, &module, old_module.is_some()) {
        let error = compilation_error!(CircularImportDependency {
            origin: modules.get_name(module_id).unwrap().to_string(),
            import_chain: cycle
                .into_iter()
                .map(|index| modules
                    .get_name(ModuleId::from_index(index))
                    .unwrap()
                    .to_string())
                .collect(),
            span: Location::new_synthesized(),
        });
        let path_for_new = module_ref.into_path();
        process_compilation_failed(modules, path_for_new, src_info, old_module, &error);
        return Err(error);
    }

    // Compilation was successful, are any dependencies stale?
    let deps: Vec<_> = module.deps().collect();
    let deps_stale = deps.iter().any(|&dep| modules.get(dep).unwrap().stale);
    if deps_stale {
        if let Some(entry) = modules.get_mut(module_id) {
            entry.update_with_stale(src_info, old_module, deps);
            mark_stale_transitively(modules, module_id);
        } else {
            // Only reachable for ByPath when the module does not yet exist.
            if let Some(path) = module_ref.into_path() {
                modules.insert(path, ModuleEntry::new_stale(src_info, deps));
            }
        }
    } else {
        // No stale deps — store the fresh module.
        // For ByPath: consume the path out of module_ref (no extra clone).
        // For Existing: write directly through the known ID.
        match module_ref {
            ModuleRef::ByPath(path) => {
                modules.replace(path, ModuleEntry::new_fresh(src_info, module));
            }
            ModuleRef::Existing(id) => {
                *modules.get_mut(id).unwrap() = ModuleEntry::new_fresh(src_info, module);
            }
        }
        // Cascade-recompile every stale direct dependent that can be rebuilt from source.
        // Each successful recompilation recurses into its own dependents via the same
        // mechanism, so the entire reverse-dependency graph is eventually brought up to date.
        let to_recompile = stale_dependents_to_recompile(modules, module_id);
        for (dep_id, dep_source_id, dep_uses) in to_recompile {
            let _ = compile_with_source_id(
                dep_source_id,
                source_table,
                modules,
                ModuleRef::Existing(dep_id),
                dep_uses,
                None,
            );
        }
    }

    Ok(ModuleAndExpr { module_id, expr })
}

fn direct_deps(modules: &Modules, target: ModuleId) -> Vec<ModuleId> {
    modules
        .enumerate()
        .filter_map(|(id, entry, _)| entry.latest_deps.contains(&target).then_some(id))
        .collect()
}

fn mark_stale_transitively(modules: &mut Modules, root: ModuleId) {
    let mut stack = vec![root];
    while let Some(id) = stack.pop() {
        for dep_id in direct_deps(modules, id) {
            let entry = match modules.get_mut(dep_id) {
                Some(entry) => entry,
                None => continue,
            };

            if !entry.stale {
                entry.stale = true;
                stack.push(dep_id);
            }
        }
    }
}

/// Collect the data needed to recompile every stale direct dependent of `target`
/// that was originally compiled from source (i.e. has a [`ModuleSrcInfo`]).
fn stale_dependents_to_recompile(
    modules: &mut Modules,
    target: ModuleId,
) -> Vec<(ModuleId, SourceId, Uses)> {
    direct_deps(modules, target)
        .into_iter()
        .filter_map(|dep_id| {
            let entry = modules.get_mut(dep_id)?;
            if !entry.stale {
                return None;
            }
            let src_info = entry.src_info.as_mut()?;
            Some((dep_id, src_info.source_id, mem::take(&mut src_info.uses)))
        })
        .collect()
}

/// Return whether there is a cycle in the module graph.
fn find_module_deps_cycle(
    modules: &Modules,
    module_id: ModuleId,
    module: &Module,
    has_old_module: bool,
) -> Option<Vec<usize>> {
    struct ModuleNode(Vec<ModuleId>);
    impl graph::Node for ModuleNode {
        type Index = ModuleId;
        fn neighbors(&self) -> impl Iterator<Item = ModuleId> {
            self.0.iter().copied()
        }
    }

    // Build a graph node for every module that must participate in cycle detection.
    //
    // Two cases:
    //   • Re-compiling an existing module: its slot in `self.modules` currently holds
    //     a temporary dummy (placed at the start of `compile_to`).  We substitute the
    //     freshly-compiled `module`'s real deps so the cycle detector sees the truth.
    //   • Compiling a brand-new module: the slot does NOT exist in `self.modules` yet
    //     (the new `compile_to` no longer pre-inserts a placeholder).  We append the
    //     new module's node via `.chain(...)` so that `module_id.as_index()` is always
    //     a valid index into `module_graph`.
    let module_graph: Vec<_> = modules
        .enumerate()
        .map(|(id, entry, _name)| {
            let deps = if id == module_id {
                // Existing module being recompiled: use real deps, not the dummy's.
                module.deps().collect()
            } else {
                entry.latest_deps.clone()
            };
            ModuleNode(deps)
        })
        // New module case: `module_id` is not in `iter_ids()` yet, so append its node
        // at the end.  Its index will be exactly `module_id.as_index()`.
        .chain(if has_old_module {
            None
        } else {
            Some(ModuleNode(module.deps().collect()))
        })
        .collect();

    graph::find_cycle_from(&module_graph, module_id.as_index())
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
