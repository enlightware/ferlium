// Copyright 2025 Enlightware GmbH
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
        uses::{Use, UseSome, Uses},
    },
};

#[derive(new)]
pub struct ModulesResolver<'a> {
    modules: &'a Modules,
}
impl ModulesResolver<'_> {
    fn import_exists(&self, module: &ModPath, symbol: Ustr) -> bool {
        if let Some(m) = self.modules.get(module) {
            m.own_symbols().any(|n| n == symbol)
        } else {
            false
        }
    }

    fn list_importable_symbols(&self, module: &ModPath) -> Box<dyn Iterator<Item = Ustr> + '_> {
        if let Some(m) = self.modules.get(module) {
            Box::new(m.own_symbols())
        } else {
            Box::new(std::iter::empty())
        }
    }
}

/// Flatten a list of `UseTree`s into `Uses` and validate explicit imports.
/// Updates `uses` in place.
///
/// Validation performed (explicit `Name` imports only):
/// - `NameImportedMultipleTimes`: same *introduced* name imported twice.
/// - `NameImportedConflictsWithLocalDefinition`: name already defined locally.
/// - `ImportNotFound`: imported symbol doesn't exist (if `exists` is provided).
///
/// Notes:
/// - `Glob` entries are flattened into `Use::All(...)` but NOT expanded.
pub fn resolve_imports(
    trees: &[UseTree],
    local_names: &HashMap<Ustr, Location>,
    resolver: &ModulesResolver<'_>,
    uses: &mut Uses,
) -> Result<(), InternalCompilationError> {
    // Track names introduced by imports (explicit and glob-expanded for conflict checking).
    let mut seen: HashMap<Ustr, ImportSite> = HashMap::new();
    prefill_seen_from_existing_uses(uses, local_names, resolver, &mut seen)?;
    let mut use_index_by_module: HashMap<ModPath, usize> = HashMap::new();

    for t in trees {
        resolve_one(
            t,
            None,
            local_names,
            &mut seen,
            uses,
            &mut use_index_by_module,
            resolver,
        )?;
    }

    Ok(())
}

fn prefill_seen_from_existing_uses(
    existing_uses: &Uses,
    defined_names: &HashMap<Ustr, Location>,
    resolver: &ModulesResolver<'_>,
    seen: &mut HashMap<Ustr, ImportSite>,
) -> Result<(), InternalCompilationError> {
    for u in existing_uses {
        match u {
            Use::Some(UseSome { module, symbols }) => {
                for sym in symbols {
                    let site = ImportSite {
                        module: module.clone(),
                        symbol: sym.0,
                        span: sym.1,
                        kind: ImportKind::Explicit,
                    };
                    register_import(sym.0, site, defined_names, seen)?;
                }
            }

            Use::All(module, span) => {
                for sym in resolver.list_importable_symbols(module) {
                    let site = ImportSite {
                        module: module.clone(),
                        symbol: sym,
                        span: *span,
                        kind: ImportKind::Glob,
                    };
                    register_import(sym, site, defined_names, seen)?;
                }
            } // future-proofing
              /*Use::Module { alias, target, span } => {
                  let site = ImportSite {
                      module: target.clone(),
                      symbol: *alias,
                      span: *span,
                      kind: ImportKind::Explicit,
                  };
                  register_import(*alias, site, defined_names, seen)?;
              }*/
        }
    }
    Ok(())
}

fn resolve_one(
    tree: &UseTree,
    base: Option<&AstPath>,
    local_names: &HashMap<Ustr, Location>,
    seen: &mut HashMap<Ustr, ImportSite>,
    uses: &mut Uses,
    use_index_by_module: &mut HashMap<ModPath, usize>,
    resolver: &ModulesResolver<'_>,
) -> Result<(), InternalCompilationError> {
    use UseTree::*;
    match tree {
        Glob(opt_path, span) => {
            let full = join_base_and_opt_path(base, opt_path.as_ref());
            let module = ast_to_module_path(&full);

            // Keep existing semantics: record the glob for later lookup.
            uses.push(Use::All(module.clone(), *span));

            // Conflict detection by enumerating all importable symbols of that module.
            let glob_span = glob_span_for(&full);

            for sym in resolver.list_importable_symbols(&module) {
                let site = ImportSite {
                    module: module.clone(),
                    symbol: sym,
                    span: glob_span,
                    kind: ImportKind::Glob,
                };
                register_import(sym, site, local_names, seen)?;
            }

            Ok(())
        }

        Group(opt_path, children) => {
            let new_base = join_base_and_opt_path(base, opt_path.as_ref());
            for c in children {
                resolve_one(
                    c,
                    Some(&new_base),
                    local_names,
                    seen,
                    uses,
                    use_index_by_module,
                    resolver,
                )?;
            }
            Ok(())
        }

        Name(rel_path) => {
            let full = join_opt_base_and_path(base, rel_path);

            let (module, symbol, span) = split_module_and_symbol(&full);
            let site = ImportSite {
                module: module.clone(),
                symbol,
                span,
                kind: ImportKind::Explicit,
            };

            // Check existence first for a nicer error in case of typos.
            if !resolver.import_exists(&module, symbol) {
                return Err(internal_compilation_error!(ImportNotFound {
                    name: symbol,
                    import_site: site,
                }));
            }

            // Then apply collision checks (also marks the name as seen).
            register_import(symbol, site.clone(), local_names, seen)?;

            // Emit `Use::Some` entry, grouped by module.
            let idx = if let Some(idx) = use_index_by_module.get(&module).copied() {
                idx
            } else {
                let idx = uses.len();
                uses.push(Use::Some(UseSome {
                    module: module.clone(),
                    symbols: Vec::new(),
                }));
                use_index_by_module.insert(module.clone(), idx);
                idx
            };
            uses[idx]
                .as_some_mut()
                .unwrap()
                .symbols
                .push((symbol, span));

            Ok(())
        }
    }
}

/// Checks collisions and records the import in `seen` if OK.
fn register_import(
    name: Ustr,
    site: ImportSite,
    defined_names: &HashMap<Ustr, Location>,
    seen: &mut HashMap<Ustr, ImportSite>,
) -> Result<(), InternalCompilationError> {
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

    // 2) imported twice? (explicit/explicit, glob/glob, or explicit/glob)
    if let Some(first_site) = seen.get(&name) {
        use ImportKind::*;

        // Case 1: explicit + explicit => always error (even if redundant)
        if first_site.kind == Explicit && site.kind == Explicit {
            return Err(internal_compilation_error!(NameImportedMultipleTimes {
                name,
                first_occurrence: first_site.clone(),
                second_occurrence: site,
            }));
        }

        // Case 2: at least one side is glob:
        // Allow only if it’s redundant (same origin).
        if first_site.module == site.module && first_site.symbol == site.symbol {
            // Optional: keep explicit site if present (nicer error spans later).
            if first_site.kind == Glob && site.kind == Explicit {
                seen.insert(name, site);
            }
            return Ok(());
        }

        // Otherwise glob introduces a different origin than the other import => error
        return Err(internal_compilation_error!(NameImportedMultipleTimes {
            name,
            first_occurrence: first_site.clone(),
            second_occurrence: site,
        }));
    }

    // record
    seen.insert(name, site);
    Ok(())
}

/// Best-effort span to attribute glob-imported names to.
/// Prefer the last segment span if present; otherwise return a default-ish span.
fn glob_span_for(p: &AstPath) -> Location {
    p.segments
        .last()
        .map(|(_, span)| *span)
        .expect("non-empty path for glob import")
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
