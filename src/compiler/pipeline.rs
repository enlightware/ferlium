// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use std::mem;

use lalrpop_util::ErrorRecovery;

use crate::{
    Location, SourceId, SourceTable, compilation_error,
    compiler::error::{CompilationError, LocatedError},
    compiler::session::{AstInspectorCb, ModuleAndExpr, ModuleEntry, ModuleSrcInfo, Modules},
    containers::b,
    format::FormatWith,
    graph,
    hir::emit_ir::{EmitModuleFrom, emit_expr, emit_module},
    module::{Module, ModuleEnv, ModuleId, Path, Uses, id::Id},
    parser::ast::{self, PExprArena, UnstableCollector, VisitExpr},
    parser::{self, describe_parse_error},
    std::new_module_using_std,
};

pub(crate) enum ModuleRef {
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
pub(crate) fn compile_with_source_id(
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

    // Emit HIR for the module.
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

    // Emit HIR for the expression, if any.
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

    // Emit HIR for the module.
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
pub(crate) fn new_ast_arena_sized_from_source(src: &str) -> PExprArena {
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
