// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use derive_new::new;
use std::collections::HashMap;
use ustr::Ustr;

use crate::{
    Location,
    ast::{Path as AstPath, UseTree},
    error::{ImportKind, ImportSite, InternalCompilationError},
    internal_compilation_error,
    module::{
        Modules,
        path::Path as ModPath,
        uses::{UseData, Uses},
    },
};

#[derive(new)]
pub struct ModulesResolver<'a> {
    modules: &'a Modules,
}
impl ModulesResolver<'_> {
    fn import_exists(&self, module: &ModPath, symbol: Ustr) -> bool {
        if let Some(m) = self.modules.get_value_by_name(module) {
            m.own_symbols().any(|n| n == symbol)
        } else {
            false
        }
    }
    fn module_exists(&self, module: &ModPath) -> bool {
        self.modules.get_value_by_name(module).is_some()
    }
}

/// Flatten a list of `UseTree`s into `Uses` and validate explicit imports.
/// Updates `uses` in place.
///
/// Validation performed (explicit `Name` imports only):
/// - `NameImportedMultipleTimes`: same *introduced* name imported twice.
/// - `NameImportedConflictsWithLocalDefinition`: name already defined locally.
/// - `ImportNotFound`: imported symbol doesn't exist.
///
/// Notes:
/// - `Glob` entries are flattened into `Use::All(...)` but NOT expanded.
pub fn resolve_imports(
    trees: &[UseTree],
    local_names: &HashMap<Ustr, Location>,
    resolver: &ModulesResolver<'_>,
    uses: &mut Uses,
) -> Result<(), InternalCompilationError> {
    // Track names introduced by explicit imports for conflict checking.
    let mut seen: HashMap<Ustr, ImportSite> = HashMap::new();
    prefill_seen_from_existing_uses(uses, local_names, &mut seen)?;

    for t in trees {
        resolve_one(t, None, local_names, &mut seen, uses, resolver)?;
    }

    Ok(())
}

fn prefill_seen_from_existing_uses(
    existing_uses: &Uses,
    defined_names: &HashMap<Ustr, Location>,
    seen: &mut HashMap<Ustr, ImportSite>,
) -> Result<(), InternalCompilationError> {
    for (&symbol, use_data) in &existing_uses.explicits {
        let site = ImportSite {
            module: use_data.module.clone(),
            span: use_data.span,
            kind: ImportKind::Symbol(symbol),
        };
        register_import(symbol, site, defined_names, seen)?;
    }
    Ok(())
}

fn resolve_one(
    tree: &UseTree,
    base: Option<&AstPath>,
    local_names: &HashMap<Ustr, Location>,
    seen: &mut HashMap<Ustr, ImportSite>,
    uses: &mut Uses,
    resolver: &ModulesResolver<'_>,
) -> Result<(), InternalCompilationError> {
    use UseTree::*;
    match tree {
        Glob(opt_path, span) => {
            let full = join_base_and_opt_path(base, opt_path.as_ref());
            let module = ast_to_module_path(&full);

            if !resolver.module_exists(&module) {
                let fused_span = Location::fuse([full.span().unwrap(), *span]).unwrap();
                return Err(internal_compilation_error!(ImportNotFound(ImportSite {
                    module: module.clone(),
                    span: fused_span,
                    kind: ImportKind::Module,
                },)));
            }

            // Record the glob for later lookup.
            uses.wildcards.push(UseData::new(module, *span));

            Ok(())
        }

        Group(opt_path, children) => {
            let new_base = join_base_and_opt_path(base, opt_path.as_ref());
            for c in children {
                resolve_one(c, Some(&new_base), local_names, seen, uses, resolver)?;
            }
            Ok(())
        }

        Name(rel_path) => {
            let full = join_opt_base_and_path(base, rel_path);

            let (module, symbol, span) = split_module_and_symbol(&full);

            // Check module first and then symbol existence.
            if !resolver.module_exists(&module) {
                return Err(internal_compilation_error!(ImportNotFound(ImportSite {
                    module: module.clone(),
                    span: full.span().unwrap(),
                    kind: ImportKind::Module,
                },)));
            }
            let site = ImportSite {
                module: module.clone(),
                span,
                kind: ImportKind::Symbol(symbol),
            };
            if !resolver.import_exists(&module, symbol) {
                return Err(internal_compilation_error!(ImportNotFound(site)));
            }

            // Then apply collision checks (also marks the name as seen).
            register_import(symbol, site, local_names, seen)?;

            // Record in uses.
            uses.explicits.insert(symbol, UseData::new(module, span));

            Ok(())
        }
    }
}

/// Checks collisions and records the import in `seen` if OK.
/// Only explicit imports are checked for collisions.
fn register_import(
    name: Ustr,
    site: ImportSite,
    defined_names: &HashMap<Ustr, Location>,
    seen: &mut HashMap<Ustr, ImportSite>,
) -> Result<(), InternalCompilationError> {
    // Only check for Explicit imports.
    // Glob imports do not conflict with anything at this stage.
    if site.kind.is_module() {
        return Ok(());
    }

    // 1) conflicts with local definition?
    if let Some(def_span) = defined_names.get(&name) {
        return Err(internal_compilation_error!(
            ImportConflictsWithLocalDefinition {
                name,
                definition_span: *def_span,
                import_site: site,
            },
        ));
    }

    // 2) imported twice? (explicit vs explicit)
    if let Some(first_site) = seen.get(&name) {
        return Err(internal_compilation_error!(NameImportedMultipleTimes {
            name,
            occurrences: vec![first_site.clone(), site,],
        }));
    }

    // record
    seen.insert(name, site);
    Ok(())
}

/// Join a base AST path with an optional AST path.
fn join_base_and_opt_path(base: Option<&AstPath>, opt: Option<&AstPath>) -> AstPath {
    let mut segments = Vec::new();
    if let Some(base) = base {
        segments.extend_from_slice(&base.segments);
    }
    if let Some(path) = opt {
        segments.extend_from_slice(&path.segments);
    }
    AstPath::new(segments)
}

/// Join an optional base AST path with another AST path, treated as relative.
fn join_opt_base_and_path(base: Option<&AstPath>, p: &AstPath) -> AstPath {
    let mut segments = Vec::new();
    if let Some(base) = base {
        segments.extend_from_slice(&base.segments);
    }
    segments.extend_from_slice(&p.segments);
    AstPath::new(segments)
}

/// Split an AST path into (module_path, symbol, symbol_span).
fn split_module_and_symbol(p: &AstPath) -> (ModPath, Ustr, Location) {
    let (last, prefix) = p.segments.split_last().expect("non-empty path");
    let (symbol, span) = *last;
    let module = ModPath::new(prefix.iter().map(|(u, _)| *u).collect());
    (module, symbol, span)
}

fn ast_to_module_path(p: &AstPath) -> ModPath {
    ModPath::new(p.segments.iter().map(|(u, _)| *u).collect())
}
