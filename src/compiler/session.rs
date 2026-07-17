// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use ::std::{cell::RefCell, fmt, sync::LazyLock};
use derive_new::new;
use itertools::Itertools;

use crate::{
    FxHashSet, Location, SourceId, SourceTable, ast, compilation_error,
    compiler::diagnostics::ModuleDiagnostic,
    compiler::error::{CompilationError, InternalCompilationError, LocatedError},
    compiler::pipeline::{
        ModuleRef, compile_with_source_id, new_ast_arena_sized_from_source, parse_module_and_expr,
    },
    define_id_type, emit_ssa,
    eval::{EvalCtx, ValOrMut, eval_function_with_ctx},
    execution::{DEFAULT_INTERACTIVE_FUEL_LIMIT, ReferenceInterpreterLimits},
    format::FormatWith,
    hir::emit_expr::emit_expr_entry_with_private_impls,
    hir::value::Value,
    hir::{self, hir_syn::local},
    module::{
        self, LocalFunctionId, Module, ModuleEnv, ModuleFunction, ModuleId, Path,
        ResolvedValueLayout, Uses,
        id::{Id, NamedIndexed},
    },
    parser::{self, describe_parse_error},
    std::{self as ferlium_std, STD_MODULE_ID, new_module_using_std, value::value_layout_for_type},
    types::r#type::Type,
};

/// A compiled module and an expression (if any).
#[derive(Debug)]
pub struct CompilationOutput {
    pub module_id: ModuleId,
    pub expr: Option<LocalFunctionId>,
}

pub(crate) type AstInspectorCb<'a> =
    &'a dyn Fn(&ast::PModule, Option<ast::PExprId>, &ast::PExprArena, &Modules);

static FIRST_USER_MODULE_ID: ModuleId = ModuleId::new(3);

thread_local! {
    static EMPTY_COMPILER_SESSION_CACHE: RefCell<Option<CompilerSession>> = const { RefCell::new(None) };
}

static DEFINED_TYPE_PARSER: LazyLock<parser::DefinedTypeParser> =
    LazyLock::new(parser::DefinedTypeParser::new);
static HOLED_TYPE_PARSER: LazyLock<parser::HoledTypeParser> =
    LazyLock::new(parser::HoledTypeParser::new);

define_id_type!(
    /// Source version of a source-backed module within a compiler session.
    SourceVersion
);

define_id_type!(
    /// Compilation attempt revision of a module within a compiler session.
    CompilationRevision
);

/// Latest source snapshot for a source-backed module.
#[derive(Debug, Clone, Copy)]
pub struct ModuleSource<'a> {
    pub source_id: SourceId,
    pub source_version: SourceVersion,
    pub source: &'a str,
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
    /// Must be non-`None` if `stale` is false.
    pub(crate) module: Option<Module>,
    /// Compilation error, if last compilation failed.
    pub(crate) last_error: Option<CompilationError>,
    /// Deps from latest successful self build, stale or not.
    pub(crate) latest_deps: Vec<ModuleId>,
    /// Latest compilation attempt revision.
    pub(crate) compilation_revision: CompilationRevision,
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
        ModuleEntry {
            src_info: Some(src_info),
            module: Some(module),
            last_error: None,
            latest_deps: deps,
            compilation_revision,
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

    pub(crate) fn next_compilation_revision(&self) -> CompilationRevision {
        CompilationRevision::from_index(self.compilation_revision.as_index() + 1)
    }
}

/// Read-only metadata view over a registered module entry.
#[derive(Clone, Copy)]
pub struct ModuleInfo<'a> {
    entry: &'a ModuleEntry,
}

impl fmt::Debug for ModuleInfo<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ModuleInfo")
            .field("source_version", &self.source_version())
            .field("compilation_revision", &self.compilation_revision())
            .field("diagnostics", &self.diagnostics())
            .field("latest_deps", &self.latest_deps())
            .field("stale", &self.is_stale())
            .field("has_compiled_module", &self.has_compiled_module())
            .finish()
    }
}

impl<'a> ModuleInfo<'a> {
    fn new(entry: &'a ModuleEntry) -> Self {
        Self { entry }
    }

    /// Latest source version for modules backed by Ferlium source.
    pub fn source_version(&self) -> Option<SourceVersion> {
        self.entry.src_info.as_ref().map(|info| info.source_version)
    }

    /// Latest compilation attempt revision.
    pub fn compilation_revision(&self) -> CompilationRevision {
        self.entry.compilation_revision
    }

    /// Diagnostics produced by the latest compilation attempt.
    pub fn diagnostics(&self) -> &'a [ModuleDiagnostic] {
        &self.entry.diagnostics
    }

    /// Dependencies discovered during the latest successful self build.
    pub fn latest_deps(&self) -> &'a [ModuleId] {
        &self.entry.latest_deps
    }

    /// Return whether this module or one of its dependencies is stale.
    pub fn is_stale(&self) -> bool {
        self.entry.stale
    }

    /// Return whether a compiled module is available for semantic fallback.
    pub fn has_compiled_module(&self) -> bool {
        self.entry.module.is_some()
    }
}

/// Internal module storage indexed both by path and by numeric ID.
pub(crate) type Modules = NamedIndexed<Path, ModuleId, ModuleEntry>;

/// Read-only view over the modules stored in a compilation session.
#[derive(Clone, Copy)]
pub struct ModuleRegistry<'a> {
    modules: &'a Modules,
}

impl<'a> ModuleRegistry<'a> {
    /// Create a registry view from internal module storage.
    pub(crate) fn new(modules: &'a Modules) -> Self {
        Self { modules }
    }

    /// Return the next module ID that would be assigned by this session.
    pub fn next_id(self) -> ModuleId {
        self.modules.next_id()
    }

    /// Return the compiled module for an ID, if one is available.
    pub fn get(self, module_id: ModuleId) -> Option<&'a Module> {
        self.modules.get(module_id)?.module()
    }

    /// Return read-only metadata for a registered module.
    pub fn info(self, module_id: ModuleId) -> Option<ModuleInfo<'a>> {
        Some(ModuleInfo::new(self.modules.get(module_id)?))
    }

    /// Return whether a module ID is registered in this session.
    pub fn contains(self, module_id: ModuleId) -> bool {
        self.modules.get(module_id).is_some()
    }

    /// Return the path registered for a module ID, if any.
    pub fn path(self, module_id: ModuleId) -> Option<&'a Path> {
        self.modules.get_name(module_id)
    }

    /// Return the module ID currently associated with a path.
    pub fn id_by_path(self, path: &Path) -> Option<ModuleId> {
        self.modules.get_id_by_name(path)
    }

    /// Return the compiled module currently associated with a path.
    pub fn get_by_path(self, path: &Path) -> Option<(ModuleId, &'a Module)> {
        let (module_id, entry) = self.modules.get_by_name(path)?;
        Some((module_id, entry.module()?))
    }

    /// Iterate over all registered module paths.
    pub fn iter_paths(self) -> impl Iterator<Item = &'a Path> {
        self.modules.iter_names()
    }

    /// Iterate over named modules that currently have compiled module data.
    pub fn iter_named_modules(self) -> impl Iterator<Item = (&'a Path, &'a Module)> {
        self.modules
            .iter_named()
            .filter_map(|(path, entry)| entry.module().map(|module| (path, module)))
    }

    /// Iterate over all registered module entries with their IDs and optional paths.
    pub fn iter_entries(
        self,
    ) -> impl Iterator<Item = (ModuleId, Option<&'a Path>, ModuleInfo<'a>)> {
        self.modules
            .enumerate()
            .map(|(module_id, entry, path)| (module_id, path, ModuleInfo::new(entry)))
    }

    /// Build a module environment for a compiled module in this registry.
    pub fn env_for(self, module: &'a Module) -> ModuleEnv<'a> {
        ModuleEnv::new(module, self.modules)
    }

    /// Return the raw internal module storage for crate internals.
    pub(crate) fn raw(self) -> &'a Modules {
        self.modules
    }
}

/// A compilation session, that contains a source table and the standard library.
#[derive(Debug, Clone)]
pub struct CompilerSession {
    /// Source table for this compilation session.
    pub(crate) source_table: SourceTable,
    /// All compiled modules
    pub(crate) modules: Modules,
    /// Pre-created empty module just using the standard library, for debugging purposes.
    pub(crate) empty_std_user: ModuleId,
    /// Stable module slot used transiently by the fixed expression-evaluation helpers.
    scratch_module: ModuleId,
    /// Initial size of the source table, for reset().
    pub(crate) initial_source_table_size: usize,
    /// Explicit feature capabilities enabled for source compiled through this session.
    pub(crate) capabilities: CompilationCapabilities,
}

#[derive(Debug, Clone, Copy, Default)]
pub struct CompilationCapabilities {
    pub allow_experimental: bool,
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
        let empty_std_user = new_module_using_std(
            modules.next_id(),
            module::Path::single_str("$empty_std_user"),
        );
        let empty_std_user = modules.insert(
            module::Path::single_str("$empty_std_user"),
            ModuleEntry::new_fresh_raw(empty_std_user),
        );
        let scratch_path = module::Path::single_str("$scratch");
        let scratch_module = new_module_using_std(modules.next_id(), scratch_path.clone());
        let scratch_module =
            modules.insert(scratch_path, ModuleEntry::new_fresh_raw(scratch_module));
        assert_eq!(modules.next_id(), FIRST_USER_MODULE_ID);
        let initial_source_table_size = source_table.len();
        let session = Self {
            source_table,
            modules,
            empty_std_user,
            scratch_module,
            initial_source_table_size,
            capabilities: CompilationCapabilities::default(),
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

    pub fn compilation_capabilities(&self) -> CompilationCapabilities {
        self.capabilities
    }

    pub fn set_allow_experimental(&mut self, allow: bool) {
        self.capabilities.allow_experimental = allow;
    }

    /// Get a read-only view of modules in this compilation session.
    pub fn modules(&self) -> ModuleRegistry<'_> {
        ModuleRegistry::new(&self.modules)
    }

    /// Get the internal module storage for compiler internals.
    pub(crate) fn raw_modules(&self) -> &Modules {
        &self.modules
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
    /// update with identical source text. Query [`CompilerSession::modules`]
    /// after a successful update to inspect the resulting module metadata.
    pub fn update_module_source(
        &mut self,
        module_id: ModuleId,
        new_source: &str,
    ) -> Result<(), String> {
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
            self.capabilities,
            None,
        );
        Ok(())
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

    fn pristine_scratch_entry(&self) -> ModuleEntry {
        ModuleEntry::new_fresh_raw(new_module_using_std(
            self.scratch_module,
            Path::single_str("$scratch"),
        ))
    }

    fn clear_scratch_entry(&mut self) {
        let pristine = self.pristine_scratch_entry();
        *self.modules.get_mut(self.scratch_module).unwrap() = pristine;
    }

    /// Compile and evaluate one of the fixed internal expressions as a client of `module_id`.
    fn eval_expr_using_module(
        &mut self,
        source_name: &str,
        source: &str,
        module_id: ModuleId,
        bindings: Vec<(&str, Type, Value)>,
        fuel_limit: Option<usize>,
    ) -> Result<Value, String> {
        assert_ne!(module_id, self.scratch_module);
        let target_path = self
            .modules
            .get_name(module_id)
            .unwrap_or_else(|| panic!("module {module_id} has no registered path"))
            .clone();
        self.expect_fresh_module(module_id);

        let (locals, values): (Vec<_>, Vec<_>) = bindings
            .into_iter()
            .map(|(name, ty, value)| (local(name, ty), value))
            .unzip();
        let discard_values = |values: Vec<Value>| {
            for value in values {
                value.discard_storage();
            }
        };

        let source_table_len = self.source_table.len();
        let source_id = self
            .source_table
            .add_source(source_name.to_string(), source.to_string());
        let (module_ast, expr_ast, arena) = match parse_module_and_expr(source, source_id, true) {
            Ok(parsed) => parsed,
            Err(error) => {
                let error = compilation_error!(ParsingFailed(error));
                let error = format!("{}", error.format_with(self.source_table()));
                discard_values(values);
                self.source_table.truncate(source_table_len);
                return Err(error);
            }
        };
        assert!(
            module_ast.is_empty(),
            "the private expression helper does not accept declarations"
        );
        let expr_ast = expr_ast.expect("internal expression source must contain an expression");

        let mut scratch = new_module_using_std(self.scratch_module, Path::single_str("$scratch"));
        scratch.add_wildcard_use(target_path, Location::new_synthesized());
        let entry_id = match emit_expr_entry_with_private_impls(
            expr_ast,
            &arena,
            &mut scratch,
            &self.modules,
            locals,
            self.capabilities,
            module_id,
        ) {
            Ok(entry_id) => entry_id,
            Err(error) => {
                let env = ModuleEnv::new(&scratch, &self.modules);
                let error = CompilationError::resolve_types(error, &env, &self.source_table);
                let error = format!("{}", error.format_with(self.source_table()));
                discard_values(values);
                self.source_table.truncate(source_table_len);
                return Err(error);
            }
        };
        *self.modules.get_mut(self.scratch_module).unwrap() = ModuleEntry::new_fresh_raw(scratch);

        let result = {
            let limits = ReferenceInterpreterLimits::default().with_fuel_limit(fuel_limit);
            let mut ctx = EvalCtx::with_limits(self.scratch_module, self, limits);
            match eval_function_with_ctx(
                self.scratch_module,
                entry_id,
                values.into_iter().map(ValOrMut::Val).collect(),
                &mut ctx,
            )
            .map(|value| value.into_value())
            {
                Ok(value) => Ok(value),
                Err(error) => Err(format!(
                    "{}",
                    error.format_with(&(self.source_table(), self.raw_modules()))
                )),
            }
        };
        self.clear_scratch_entry();
        self.source_table.truncate(source_table_len);
        result
    }

    /// Render a value by evaluating Ferlium's `to_string(value)` in `module_id`.
    pub fn value_to_string(
        &mut self,
        module_id: ModuleId,
        value: Value,
        ty: Type,
    ) -> Result<String, String> {
        self.value_to_string_with_fuel(module_id, value, ty, Some(DEFAULT_INTERACTIVE_FUEL_LIMIT))
    }

    /// Render a value by evaluating Ferlium's `to_string(value)` with an optional fuel limit.
    pub fn value_to_string_with_fuel(
        &mut self,
        module_id: ModuleId,
        value: Value,
        ty: Type,
        fuel_limit: Option<usize>,
    ) -> Result<String, String> {
        match self.eval_expr_using_module(
            "<value_to_string>",
            "to_string(value)",
            module_id,
            vec![("value", ty, value)],
            fuel_limit,
        ) {
            Ok(rendered) => rendered
                .into_primitive_ty::<crate::std::string::String>()
                .map(|rendered| rendered.to_string())
                .ok_or_else(|| "to_string(value) did not return a string".to_string()),
            Err(error) => Err(error),
        }
    }

    /// Render a value for interactive inspection by evaluating `inspect(value)`.
    pub fn value_to_inspect_text(
        &mut self,
        module_id: ModuleId,
        value: Value,
        ty: Type,
    ) -> Result<String, String> {
        self.value_to_inspect_text_with_fuel(
            module_id,
            value,
            ty,
            Some(DEFAULT_INTERACTIVE_FUEL_LIMIT),
        )
    }

    /// Render a value for interactive inspection with an optional fuel limit.
    pub fn value_to_inspect_text_with_fuel(
        &mut self,
        module_id: ModuleId,
        value: Value,
        ty: Type,
        fuel_limit: Option<usize>,
    ) -> Result<String, String> {
        match self.eval_expr_using_module(
            "<value_to_inspect_text>",
            "inspect(value)",
            module_id,
            vec![("value", ty, value)],
            fuel_limit,
        ) {
            Ok(rendered) => rendered
                .into_primitive_ty::<crate::std::string::String>()
                .map(|rendered| rendered.to_string())
                .ok_or_else(|| "inspect(value) did not return a string".to_string()),
            Err(error) => Err(error),
        }
    }

    pub fn default_value_for_type(&mut self, ty: Type) -> Option<Value> {
        if ty.data().is_variable() {
            return None;
        }

        let module_env = self.module_env();
        let source = format!("(default(): {})", ty.format_with(&module_env));
        self.eval_expr_using_module(
            "<default_value_for_type>",
            &source,
            self.empty_std_user,
            vec![],
            None,
        )
        .ok()
    }

    /// Reset the compiler session to its initial state, without rebuilding std.
    pub fn reset(&mut self) {
        self.clear_scratch_entry();
        // We only keep std, $empty_std_user, and $scratch and drop the rest.
        self.modules.truncate(FIRST_USER_MODULE_ID.as_index());
        self.source_table.truncate(self.initial_source_table_size);
    }

    /// Register a module without Ferlium source in this compilation session and return its id.
    pub fn register_module(&mut self, path: module::Path, module: Module) -> ModuleId {
        log::trace!("Registering module {path}");
        let module_id = self
            .modules
            .insert(path, ModuleEntry::new_fresh_raw(module));
        log::trace!("Registered module received id {module_id}");
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
        let ty = DEFINED_TYPE_PARSER
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
        let ty = HOLED_TYPE_PARSER
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
    ) -> Result<CompilationOutput, CompilationError> {
        if log::log_enabled!(log::Level::Trace) {
            log::trace!(
                "Using other modules: {}",
                self.modules.iter_names().join(", ")
            );
        }
        if log::log_enabled!(log::Level::Trace) {
            log::trace!("Input: {src_code}");
        }

        // Compile the code.
        // If trace logging is enabled, prepare an AST inspector that logs the ASTs.
        let uses = Uses::new_with_std();
        let output = if log::log_enabled!(log::Level::Trace) {
            let dbg_module =
                new_module_using_std(self.modules.next_id(), Path::single_str("$debug"));
            let ast_inspector = |module_ast: &ast::PModule,
                                 expr_ast: Option<ast::PExprId>,
                                 arena: &ast::PExprArena,
                                 modules: &Modules| {
                let env = ModuleEnv::new(&dbg_module, modules);
                let ast = ast::ModuleDisplay::new(module_ast, arena);
                log::trace!("Module AST\n{}", ast.format_with(&env));
                if let Some(expr_ast) = expr_ast {
                    let ast = ast::ExprDisplay::new(expr_ast, arena);
                    log::trace!("Expr AST\n{}", ast.format_with(&env));
                }
            };
            self.compile_to_with_ast_inspector(
                src_code,
                source_name,
                module_path,
                uses,
                Some(&ast_inspector),
            )
        } else {
            self.compile_to_with_ast_inspector(src_code, source_name, module_path, uses, None)
        }?;

        // If trace logging is enabled, display the final HIR after linking and finalizing pending functions.
        if log::log_enabled!(log::Level::Trace) {
            let entry = self.modules.get(output.module_id).unwrap();
            if let Some(module) = &entry.module {
                if !module.is_empty() {
                    log::trace!("Module HIR\n{}", module.format_with(&self.modules));
                }
                if let Some(expr) = output.expr {
                    let env = ModuleEnv::new(module, &self.modules);
                    let function = module.get_function_by_id(expr).unwrap();
                    let script = function.code.as_script().unwrap();
                    log::trace!(
                        "Expr HIR\n{}",
                        hir::ExprDisplay::new(script.entry_node_id, &function.locals)
                            .format_with(&env)
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
    ) -> Result<CompilationOutput, CompilationError> {
        self.compile_to_with_ast_inspector(src_code, source_name, module_path, uses, None)
    }

    pub(crate) fn compile_to_with_ast_inspector(
        &mut self,
        src_code: &str,
        source_name: &str,
        module_path: Path,
        uses: Uses,
        ast_inspector: Option<AstInspectorCb<'_>>,
    ) -> Result<CompilationOutput, CompilationError> {
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
            self.capabilities,
            ast_inspector,
        )
    }

    /// Compiles `src` with std-only uses and emits its SSA form. Panics on compilation failure;
    /// for source that is already compiled (e.g. with custom uses), use
    /// [`emit_ssa_module`](Self::emit_ssa_module) instead.
    pub fn emit_ssa(&mut self, source_name: &str, src: &str) -> String {
        let p = module::Path::single_str(source_name);
        let i = self.compile(src, source_name, p).unwrap().module_id;
        self.emit_ssa_module(i)
    }

    /// Emits the SSA form of the already-compiled module `module_id`.
    pub fn emit_ssa_module(&mut self, module_id: ModuleId) -> String {
        let module = self.expect_fresh_module(module_id);
        emit_ssa::emit_ssa(module, self.raw_modules(), self)
    }

    /// Lowers `src` to SSA and interprets its `fn main` entry, returning a textual rendering of the
    /// result. Used to check that the SSA lowering is semantically correct.
    ///
    /// The source must define a no-argument `fn main`; its lowered body (and the bodies of any
    /// script functions it calls) is run by the SSA interpreter, while native (std) callees are
    /// delegated to the HIR interpreter.
    pub fn eval_ssa(&mut self, source_name: &str, src: &str) -> String {
        use crate::ssa::interpreter::Interpreter;

        let p = module::Path::single_str(source_name);
        let module_id = self.compile(src, source_name, p).unwrap().module_id;
        let (main_id, ret_ty) = {
            let module = self.expect_fresh_module(module_id);
            let main_id = module
                .get_local_function_id(ustr::ustr("main"))
                .expect("eval_ssa requires a `fn main` entry");
            let ret_ty = module
                .get_function_by_id(main_id)
                .unwrap()
                .definition
                .ty_scheme
                .ty
                .ret;
            (main_id, ret_ty)
        };

        let value = {
            let mut interp = Interpreter::new(module_id, self);
            interp.run_main(module_id, main_id).unwrap_or_else(|error| {
                panic!("SSA interpretation raised a runtime error: {error:?}")
            })
        };

        if ret_ty == Type::unit() {
            value.discard_storage();
            return "()".to_string();
        }
        self.value_to_inspect_text(module_id, value, ret_ty)
            .unwrap_or_else(|error| panic!("rendering SSA result failed: {error}"))
    }

    /// Interpret an already-compiled expression entry through the SSA backend.
    pub fn run_entry_via_ssa(
        &self,
        module_id: ModuleId,
        entry: LocalFunctionId,
    ) -> Result<Value, crate::eval::RuntimeError> {
        use crate::ssa::interpreter::Interpreter;
        let mut interp = Interpreter::new(module_id, self);
        interp.run_entry(module_id, entry, vec![])
    }

    /// Returns the entry for module_id, or panic if not found.
    pub(crate) fn expect_module_entry(&self, module_id: ModuleId) -> &ModuleEntry {
        self.raw_modules()
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

    /// Compute the concrete value layout of `ty` in the environment of `module_id`.
    pub(crate) fn value_layout(
        &self,
        module_id: ModuleId,
        ty: Type,
        span: Location,
    ) -> Result<ResolvedValueLayout, InternalCompilationError> {
        let module = self.expect_fresh_module(module_id);
        let env = ModuleEnv::new(module, &self.modules);
        value_layout_for_type(ty, span, &env)
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
        runner: impl FnOnce(&ModuleFunction, &Module, ModuleRegistry<'_>) -> Result<R, String>,
    ) -> Result<R, String> {
        let entry = self
            .raw_modules()
            .get(module_id)
            .ok_or_else(|| format!("Module {module_id} not found"))?;
        if entry.stale {
            return Err(format!(
                "Module {module_id} is stale due to failed compilation, cannot run function {name}"
            ));
        }
        let module = entry.module().unwrap();
        match module.lookup_function(name, &self.modules) {
            Ok(Some(func)) => runner(func, module, self.modules()),
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

#[cfg(test)]
mod tests {
    use super::*;

    fn module_snapshot(
        session: &CompilerSession,
        module_id: ModuleId,
    ) -> (
        usize,
        Vec<usize>,
        Option<SourceVersion>,
        CompilationRevision,
    ) {
        let entry = session.modules.get(module_id).unwrap();
        let module = entry.module().unwrap();
        let mut deps = module.deps().map(ModuleId::as_index).collect::<Vec<_>>();
        deps.sort_unstable();
        (
            module.function_count(),
            deps,
            entry.src_info.as_ref().map(|info| info.source_version),
            entry.compilation_revision,
        )
    }

    #[test]
    fn repeated_rendering_restores_scratch_and_preserves_target_metadata() {
        let mut session = CompilerSession::new();
        let target = session
            .compile(
                "fn marker() -> int { 1 }",
                "<scratch_invariant_target>",
                Path::single_str("scratch_invariant_target"),
            )
            .unwrap()
            .module_id;
        let source_table_len = session.source_table.len();
        let scratch_before = module_snapshot(&session, session.scratch_module);
        let target_before = module_snapshot(&session, target);

        for value in [41isize, 42] {
            assert_eq!(
                session.value_to_string(target, Value::native(value), Type::primitive::<isize>()),
                Ok(value.to_string())
            );
            assert_eq!(session.source_table.len(), source_table_len);
            assert_eq!(
                module_snapshot(&session, session.scratch_module),
                scratch_before
            );
            assert_eq!(module_snapshot(&session, target), target_before);
        }

        assert!(
            session
                .eval_expr_using_module("<scratch_parse_error>", "(", target, vec![], None)
                .is_err()
        );
        assert_eq!(session.source_table.len(), source_table_len);
        assert_eq!(
            module_snapshot(&session, session.scratch_module),
            scratch_before
        );
        assert_eq!(module_snapshot(&session, target), target_before);

        assert!(
            session
                .eval_expr_using_module(
                    "<scratch_compilation_error>",
                    "1 + true",
                    target,
                    vec![],
                    None,
                )
                .is_err()
        );
        assert_eq!(session.source_table.len(), source_table_len);
        assert_eq!(
            module_snapshot(&session, session.scratch_module),
            scratch_before
        );
        assert_eq!(module_snapshot(&session, target), target_before);

        let runtime_error = session
            .eval_expr_using_module(
                "<scratch_runtime_error>",
                "loop {}",
                target,
                vec![],
                Some(0),
            )
            .unwrap_err();
        assert!(runtime_error.contains("Execution fuel exhausted"));
        assert_eq!(session.source_table.len(), source_table_len);
        assert_eq!(
            module_snapshot(&session, session.scratch_module),
            scratch_before
        );
        assert_eq!(module_snapshot(&session, target), target_before);
    }
}
