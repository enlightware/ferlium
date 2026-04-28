// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use ::std::{cell::RefCell, mem};
use derive_new::new;
use itertools::Itertools;

use crate::{
    FxHashSet, Location, SourceId, SourceTable, ast, compilation_error,
    compiler::diagnostics::ModuleDiagnostic,
    compiler::error::{CompilationError, LocatedError},
    compiler::pipeline::{
        ModuleRef, compile_with_source_id, new_ast_arena_sized_from_source, parse_module_and_expr,
    },
    containers::b,
    define_id_type,
    eval::{EvalCtx, RuntimeError, ValOrMut, eval_node_with_ctx},
    format::FormatWith,
    hir::emit_ir::{CompiledExpr, EmitModuleFrom, emit_expr, emit_module},
    hir::value::Value,
    hir::{self, hir_syn::local},
    module::{
        self, LocalDecl, Module, ModuleEnv, ModuleFunction, ModuleId, Path, Uses,
        id::{Id, NamedIndexed},
    },
    parser::{self, describe_parse_error},
    std::{self as ferlium_std, STD_MODULE_ID, new_module_using_std},
    types::r#type::Type,
};

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

thread_local! {
    static EMPTY_COMPILER_SESSION_CACHE: RefCell<Option<CompilerSession>> = const { RefCell::new(None) };
}

define_id_type!(
    /// Source version of a source-backed module within a compiler session.
    SourceVersion
);

define_id_type!(
    /// Compilation attempt revision of a module within a compiler session.
    CompilationRevision
);

/// Metadata for a module registered in a [`CompilerSession`].
#[derive(Debug, Clone)]
pub struct ModuleInfo {
    pub module_id: ModuleId,
    /// Human-readable module path, if the module has one.
    pub path: Option<Path>,
    /// Latest source version for modules backed by Ferlium source.
    pub source_version: Option<SourceVersion>,
    /// Whether this module or one of its dependencies is currently stale.
    pub stale: bool,
    /// Whether a compiled module is available for semantic fallback.
    pub has_compiled_module: bool,
}

/// Latest source snapshot for a source-backed module.
#[derive(Debug, Clone, Copy)]
pub struct ModuleSource<'a> {
    pub source_id: SourceId,
    pub source_version: SourceVersion,
    pub source: &'a str,
}

/// Result of replacing a module source and immediately attempting compilation.
#[derive(Debug, Clone)]
pub struct ModuleUpdateResult {
    pub module_id: ModuleId,
    /// Source version after the update. This is unchanged when the source text
    /// is identical to the previous source text.
    pub source_version: SourceVersion,
    /// Compilation revision produced by the update attempt.
    pub compilation_revision: CompilationRevision,
    /// Diagnostics produced by the update attempt.
    pub diagnostics: Vec<ModuleDiagnostic>,
}

/// All data needed to rebuild the module.
#[derive(Clone, Debug, new)]
pub struct ModuleSrcInfo {
    /// The source code used
    pub(crate) source_id: SourceId,
    /// The logical source version for the module.
    pub(crate) source_version: SourceVersion,
    /// The use directive used
    pub(crate) uses: Uses,
}

/// A module that has been attempted to be compiled at least once.
#[derive(Debug, Clone)]
pub struct ModuleEntry {
    /// Informations needed to rebuild the module, if it supports rebuilding (std doesn't).
    pub(crate) src_info: Option<ModuleSrcInfo>,
    /// Last good compiled module (without stale deps at that time).
    /// Must be not-None if [`stale`] is false.
    pub(crate) module: Option<Module>,
    /// Compilation error, if last compilation failed.
    pub(crate) last_error: Option<CompilationError>,
    /// Deps from latest successful self build, stale or not.
    pub(crate) latest_deps: Vec<ModuleId>,
    /// Latest compilation attempt revision.
    pub(crate) compilation_revision: CompilationRevision,
    /// Last successful source version, if this source-backed module has compiled fresh.
    pub(crate) last_successful_source_version: Option<SourceVersion>,
    /// Last successful compilation revision, if this module has compiled fresh.
    pub(crate) last_successful_compilation_revision: Option<CompilationRevision>,
    /// Diagnostics from the latest compilation attempt.
    pub(crate) diagnostics: Vec<ModuleDiagnostic>,
    /// Whether this module or some of its dependencies failed to compile.
    pub(crate) stale: bool,
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
            compilation_revision: CompilationRevision::from_index(0),
            last_successful_source_version: None,
            last_successful_compilation_revision: Some(CompilationRevision::from_index(0)),
            diagnostics: Vec::new(),
            stale: false,
        }
    }

    /// New fresh module that can be rebuilt later.
    pub fn new_fresh(
        src_info: ModuleSrcInfo,
        module: Module,
        compilation_revision: CompilationRevision,
    ) -> Self {
        let deps = module.deps().collect();
        let source_version = src_info.source_version;
        ModuleEntry {
            src_info: Some(src_info),
            module: Some(module),
            last_error: None,
            latest_deps: deps,
            compilation_revision,
            last_successful_source_version: Some(source_version),
            last_successful_compilation_revision: Some(compilation_revision),
            diagnostics: Vec::new(),
            stale: false,
        }
    }

    /// New module that compiled but whose dependencies are stale, and can be rebuilt later.
    pub fn new_stale(
        src_info: ModuleSrcInfo,
        deps: Vec<ModuleId>,
        compilation_revision: CompilationRevision,
    ) -> Self {
        ModuleEntry {
            src_info: Some(src_info),
            module: None,
            last_error: None,
            latest_deps: deps,
            compilation_revision,
            last_successful_source_version: None,
            last_successful_compilation_revision: None,
            diagnostics: Vec::new(),
            stale: true,
        }
    }

    /// New module that failed to compile but can be rebuilt later.
    pub fn new_with_error(
        src_info: ModuleSrcInfo,
        error: CompilationError,
        compilation_revision: CompilationRevision,
        diagnostics: Vec<ModuleDiagnostic>,
    ) -> Self {
        ModuleEntry {
            src_info: Some(src_info),
            module: None,
            last_error: Some(error),
            latest_deps: vec![],
            compilation_revision,
            last_successful_source_version: None,
            last_successful_compilation_revision: None,
            diagnostics,
            stale: true,
        }
    }

    /// Our module compiled successfully, but some of its dependencies are stale.
    pub fn update_with_stale(
        &mut self,
        src_info: ModuleSrcInfo,
        old_module: Option<Module>,
        latest_deps: Vec<ModuleId>,
        compilation_revision: CompilationRevision,
    ) {
        self.src_info = Some(src_info);
        self.module = old_module;
        self.last_error = None;
        self.latest_deps = latest_deps;
        self.compilation_revision = compilation_revision;
        self.diagnostics.clear();
        self.stale = true;
    }

    /// Our module failed to compile, but can be rebuilt later.
    pub fn update_with_compilation_error(
        &mut self,
        src_info: ModuleSrcInfo,
        old_module: Option<Module>,
        error: CompilationError,
        compilation_revision: CompilationRevision,
        diagnostics: Vec<ModuleDiagnostic>,
    ) {
        self.src_info = Some(src_info);
        self.module = old_module;
        self.last_error = Some(error);
        self.compilation_revision = compilation_revision;
        self.diagnostics = diagnostics;
        self.stale = true;
    }

    pub fn module(&self) -> Option<&Module> {
        self.module.as_ref()
    }

    pub fn is_stale(&self) -> bool {
        self.stale
    }

    pub fn compilation_revision(&self) -> CompilationRevision {
        self.compilation_revision
    }

    pub fn diagnostics(&self) -> &[ModuleDiagnostic] {
        &self.diagnostics
    }

    pub fn source_version(&self) -> Option<SourceVersion> {
        self.src_info.as_ref().map(|info| info.source_version)
    }

    pub fn latest_deps(&self) -> &[ModuleId] {
        &self.latest_deps
    }

    pub fn last_successful_source_version(&self) -> Option<SourceVersion> {
        self.last_successful_source_version
    }

    pub fn last_successful_compilation_revision(&self) -> Option<CompilationRevision> {
        self.last_successful_compilation_revision
    }

    pub(crate) fn next_compilation_revision(&self) -> CompilationRevision {
        CompilationRevision::from_index(self.compilation_revision.as_index() + 1)
    }
}

/// A set of modules indexed both by name (Path) and by numeric ID (ModuleId).
/// This is the canonical way to hold a collection of modules in a compilation session.
pub type Modules = NamedIndexed<Path, ModuleId, ModuleEntry>;

/// A compilation session, that contains a source table and the standard library.
#[derive(Debug, Clone)]
pub struct CompilerSession {
    /// Source table for this compilation session.
    pub(crate) source_table: SourceTable,
    /// All compiled modules
    pub(crate) modules: Modules,
    /// Pre-created empty module just using the standard library, for debugging purposes.
    pub(crate) empty_std_user: ModuleId,
    /// Initial size of the source table, for reset().
    pub(crate) initial_source_table_size: usize,
}

#[derive(Debug, Clone)]
pub(crate) enum EvalExprError {
    Compilation(CompilationError),
    Runtime(RuntimeError),
}

impl CompilerSession {
    /// Create a new compilation session with an empty source table and the standard library loaded.
    pub fn new() -> Self {
        if let Some(session) = EMPTY_COMPILER_SESSION_CACHE.with(|cache| cache.borrow().clone()) {
            return session;
        }

        let mut source_table = SourceTable::default();
        let mut modules = Modules::default();
        assert_eq!(modules.next_id(), STD_MODULE_ID);
        let std_module = ferlium_std::std_module(&mut source_table);
        let std_name = module::Path::single_str("std");
        modules.insert(std_name, ModuleEntry::new_fresh_raw(std_module));
        let empty_std_user = new_module_using_std(modules.next_id());
        let empty_std_user = modules.insert(
            module::Path::single_str("$empty_std_user"),
            ModuleEntry::new_fresh_raw(empty_std_user),
        );
        assert_eq!(modules.next_id(), FIRST_USER_MODULE_ID);
        let initial_source_table_size = source_table.len();
        let session = Self {
            source_table,
            modules,
            empty_std_user,
            initial_source_table_size,
        };

        EMPTY_COMPILER_SESSION_CACHE.with(|cache| {
            *cache.borrow_mut() = Some(session.clone());
        });

        session
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

    /// List every module registered in this session.
    pub fn list_modules(&self) -> Vec<ModuleInfo> {
        self.modules
            .enumerate()
            .map(|(module_id, entry, path)| ModuleInfo {
                module_id,
                path: path.cloned(),
                source_version: entry.src_info.as_ref().map(|info| info.source_version),
                stale: entry.stale,
                has_compiled_module: entry.module.is_some(),
            })
            .collect()
    }

    /// Get the latest source snapshot for a source-backed module.
    pub fn get_module_source(&self, module_id: ModuleId) -> Option<ModuleSource<'_>> {
        let src_info = self.modules.get(module_id)?.src_info.as_ref()?;
        let source = self.source_table.get_source_text(src_info.source_id)?;
        Some(ModuleSource {
            source_id: src_info.source_id,
            source_version: src_info.source_version,
            source,
        })
    }

    /// Get modules whose latest known dependencies include this module.
    pub fn get_module_reverse_deps(&self, module_id: ModuleId) -> Vec<ModuleId> {
        self.modules
            .enumerate()
            .filter_map(|(id, entry, _)| entry.latest_deps.contains(&module_id).then_some(id))
            .collect()
    }

    /// Get transitive reverse dependencies that may be affected if this module changes.
    pub fn get_modules_affected_by(&self, module_id: ModuleId) -> Vec<ModuleId> {
        let mut affected = Vec::new();
        let mut stack = self.get_module_reverse_deps(module_id);
        while let Some(id) = stack.pop() {
            if affected.contains(&id) {
                continue;
            }
            affected.push(id);
            stack.extend(self.get_module_reverse_deps(id));
        }
        affected
    }

    /// Replace a source-backed module's source and immediately compile it.
    ///
    /// The source version only changes when the source text changes. The
    /// compilation revision changes for every compilation attempt, including an
    /// update with identical source text.
    pub fn update_module_source(
        &mut self,
        module_id: ModuleId,
        new_source: &str,
    ) -> Result<ModuleUpdateResult, String> {
        let src_info = self
            .modules
            .get(module_id)
            .ok_or_else(|| format!("Module {module_id} not found"))?
            .src_info
            .as_ref()
            .ok_or_else(|| format!("Module {module_id} is not source-backed"))?
            .clone();
        let uses = src_info.uses.clone();
        let (source_id, source_version) =
            self.add_or_reuse_module_source(Some(&src_info), None, new_source);
        let _ = compile_with_source_id(
            source_id,
            source_version,
            &self.source_table,
            &mut self.modules,
            ModuleRef::Existing(module_id),
            uses,
            None,
        );
        let entry = self
            .modules
            .get(module_id)
            .expect("module must exist after update");
        Ok(ModuleUpdateResult {
            module_id,
            source_version,
            compilation_revision: entry.compilation_revision,
            diagnostics: entry.diagnostics.clone(),
        })
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

    fn eval_expr_with_locals_in_module(
        &mut self,
        source_name: &str,
        source: &str,
        module: &Module,
        locals: Vec<LocalDecl>,
        environment: Vec<ValOrMut>,
    ) -> Result<(Value, Type), EvalExprError> {
        let source_id = self
            .source_table
            .add_source(source_name.to_string(), source.to_string());
        let (module_ast, expr_ast, arena) = parse_module_and_expr(source, source_id, true)
            .map_err(|error| {
                EvalExprError::Compilation(compilation_error!(ParsingFailed(error)))
            })?;
        let emit_from = EmitModuleFrom::Existing(b(module.clone()));
        let mut temp_module = emit_module(
            module_ast,
            &arena,
            module.module_id(),
            &self.modules,
            emit_from,
        )
        .map_err(|error| {
            let env = ModuleEnv::new(module, &self.modules);
            EvalExprError::Compilation(CompilationError::resolve_types(
                error,
                &env,
                &self.source_table,
            ))
        })?;
        let expr_ast = expr_ast.expect("snippet source must contain an expression");
        let compiled = emit_expr(expr_ast, &arena, &mut temp_module, &self.modules, locals)
            .map_err(|error| {
                let env = ModuleEnv::new(&temp_module, &self.modules);
                EvalExprError::Compilation(CompilationError::resolve_types(
                    error,
                    &env,
                    &self.source_table,
                ))
            })?;
        let result_ty = compiled.ty.ty;
        let previous_module = {
            let entry = self
                .modules
                .get_mut(module.module_id())
                .expect("snippet base module must be registered in the session");
            let slot = entry
                .module
                .as_mut()
                .expect("snippet base module must have a compiled module");
            mem::replace(slot, temp_module)
        };

        let result = {
            let temp_module = self.expect_fresh_module(module.module_id());
            let mut ctx = EvalCtx::with_environment(module.module_id(), environment, self);
            eval_node_with_ctx(
                &temp_module.ir_arena,
                compiled.expr,
                &mut ctx,
                &compiled.locals,
            )
            .map(|value| value.into_value())
            .map_err(EvalExprError::Runtime)
        };

        let entry = self
            .modules
            .get_mut(module.module_id())
            .expect("snippet base module must still be registered in the session");
        let slot = entry
            .module
            .as_mut()
            .expect("snippet base module must still have a compiled module");
        *slot = previous_module;

        result.map(|value| (value, result_ty))
    }

    pub(crate) fn eval_expr_with_locals(
        &mut self,
        source_name: &str,
        source: &str,
        module_id: ModuleId,
        locals: Vec<LocalDecl>,
        environment: Vec<ValOrMut>,
    ) -> Result<Value, EvalExprError> {
        let module = self.expect_fresh_module(module_id).clone();
        self.eval_expr_with_locals_in_module(source_name, source, &module, locals, environment)
            .map(|(value, _ty)| value)
    }

    /// Compile and evaluate a Ferlium expression in an existing module context.
    ///
    /// The snippet is type-checked as if it appeared in `module_id`, with the
    /// supplied locals available to the expression. The target module's source,
    /// source version, and compiled module are restored after evaluation.
    pub fn eval_expression_in_module(
        &mut self,
        module_id: ModuleId,
        source_name: &str,
        source: &str,
        bindings: Vec<(&str, Type, ValOrMut)>,
    ) -> Result<(Value, Type), String> {
        let module = self.expect_fresh_module(module_id).clone();
        let (locals, environment) = bindings
            .into_iter()
            .map(|(name, ty, value)| (local(name, ty), value))
            .unzip();
        self.eval_expr_with_locals_in_module(source_name, source, &module, locals, environment)
            .map_err(|error| self.format_eval_expr_error(error))
    }

    fn format_eval_expr_error(&self, error: EvalExprError) -> String {
        match error {
            EvalExprError::Compilation(error) => {
                format!("{}", error.format_with(self.source_table()))
            }
            EvalExprError::Runtime(error) => {
                format!(
                    "{}",
                    error.format_with(&(self.source_table(), self.modules()))
                )
            }
        }
    }

    /// Render a value by evaluating Ferlium's `to_string(value)` in `module_id`.
    ///
    /// This is the same semantic formatting path used by the IDE execution
    /// view. The concrete value type is required so trait-based `to_string`
    /// resolution happens through the compiler.
    pub fn value_to_string(
        &mut self,
        module_id: ModuleId,
        value: Value,
        ty: Type,
    ) -> Result<String, String> {
        match self.eval_expr_with_locals(
            "<value_to_string>",
            "to_string(value)",
            module_id,
            vec![local("value", ty)],
            vec![ValOrMut::Val(value)],
        ) {
            Ok(rendered) => rendered
                .into_primitive_ty::<crate::std::string::String>()
                .map(|rendered| rendered.to_string())
                .ok_or_else(|| "to_string(value) did not return a string".to_string()),
            Err(error) => Err(self.format_eval_expr_error(error)),
        }
    }

    pub(crate) fn eval_std_expr_with_locals(
        &mut self,
        source_name: &str,
        source: &str,
        locals: Vec<LocalDecl>,
        environment: Vec<ValOrMut>,
    ) -> Result<Value, EvalExprError> {
        self.eval_expr_with_locals(
            source_name,
            source,
            self.empty_std_user,
            locals,
            environment,
        )
    }

    pub fn default_value_for_type(&mut self, ty: Type) -> Option<Value> {
        if ty.data().is_variable() {
            return None;
        }

        let module_env = self.module_env();
        let source = format!("(default(): {})", ty.format_with(&module_env));
        self.eval_std_expr_with_locals("<default_value_for_type>", &source, vec![], vec![])
            .ok()
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

        // If debug logging is enabled, display the final HIR, after linking and finalizing pending functions.
        if log::log_enabled!(log::Level::Debug) {
            let entry = self.modules.get(output.module_id).unwrap();
            if let Some(module) = &entry.module {
                if !module.is_empty() {
                    log::debug!("Module HIR\n{}", module.format_with(&self.modules));
                }
                if let Some(expr) = output.expr.as_ref() {
                    let env = ModuleEnv::new(module, &self.modules);
                    log::debug!(
                        "Expr HIR\n{}",
                        hir::ExprDisplay::new(expr.expr, &expr.locals).format_with(&env)
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
        let src_info = self
            .modules
            .get_by_name(&module_path)
            .and_then(|(_, entry)| entry.src_info.clone());
        let (source_id, source_version) =
            self.add_or_reuse_module_source(src_info.as_ref(), Some(source_name), src_code);

        compile_with_source_id(
            source_id,
            source_version,
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

    fn add_or_reuse_module_source(
        &mut self,
        current: Option<&ModuleSrcInfo>,
        source_name: Option<&str>,
        source: &str,
    ) -> (SourceId, SourceVersion) {
        if let Some(src_info) = current
            && self
                .source_table
                .get_source_text(src_info.source_id)
                .is_some_and(|old_source| old_source == source)
        {
            return (src_info.source_id, src_info.source_version);
        }

        let source_version = current.map_or(SourceVersion::from_index(0), |src_info| {
            SourceVersion::from_index(src_info.source_version.as_index() + 1)
        });
        let source_name = current
            .and_then(|src_info| self.source_table.get_source_name(src_info.source_id))
            .map_or_else(
                || source_name.unwrap_or("<source>").to_string(),
                ToString::to_string,
            );
        let source_id = self
            .source_table
            .add_source(source_name, source.to_string());
        (source_id, source_version)
    }
}

impl Default for CompilerSession {
    fn default() -> Self {
        CompilerSession::new()
    }
}
