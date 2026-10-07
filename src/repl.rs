// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Session imports and inspection shared by the native and Wasm REPLs.

use ustr::Ustr;

use crate::{
    CompilerSession, FxHashSet, Location, Path,
    format::FormatWith,
    hir::native_functions::NativeFnR,
    module::{LocalFunctionId, Module, ModuleId, ShowModuleWithOptions, UseData, Uses, id::Id},
    std::{new_module_using_std, string::String as FerliumString},
    types::effects::effect_write,
    ustr,
};

/// Import earlier submissions, preferring the latest definition and allowing local shadowing.
pub fn submission_uses(
    session: &CompilerSession,
    local_symbols: &FxHashSet<Ustr>,
    counter: usize,
    mut uses: Uses,
) -> Uses {
    for index in (0..counter).rev() {
        let path = Path::single_str(&format!("repl{index}"));
        if let Some((_, module)) = session.modules().get_by_path(&path) {
            for sym in module.own_symbols() {
                if !local_symbols.contains(&sym)
                    && !uses.explicits.contains_key(&sym)
                    && !sym.starts_with('$')
                    && !sym.contains("::")
                {
                    uses.explicits
                        .insert(sym, UseData::new(path.clone(), Location::new_synthesized()));
                }
            }
        }
    }
    uses
}

fn module_path(name: &str) -> Path {
    Path::new(name.split("::").map(ustr).collect())
}

/// Resolve a module available for REPL inspection.
pub fn selected_module(
    session: &CompilerSession,
    current: ModuleId,
    name: Option<&str>,
) -> Result<ModuleId, String> {
    let id = match name {
        None => current,
        Some(name) => session
            .modules()
            .id_by_path(&module_path(name))
            .ok_or_else(|| format!("Module {name} not found."))?,
    };
    if session.modules().get(id).is_none() {
        return Err(
            "Module never compiled successfully and is thus not available for inspection."
                .to_string(),
        );
    }
    if session
        .modules()
        .info(id)
        .is_some_and(|info| info.is_stale())
    {
        return Err(format!(
            "Module {} is stale and cannot be inspected.",
            name.unwrap_or("current")
        ));
    }
    Ok(id)
}

/// Render a module, including private definitions, using the REPL's display conventions.
pub fn module_text(
    session: &CompilerSession,
    current: ModuleId,
    name: Option<&str>,
) -> Result<String, String> {
    let id = selected_module(session, current, name)?;
    let module = session.modules().get(id).ok_or_else(|| {
        "Module never compiled successfully and is thus not available for inspection.".to_string()
    })?;
    let options = ShowModuleWithOptions {
        modules: session.modules(),
        show_details: false,
        show_all_functions: true,
        show_private_items: true,
    };
    Ok(module.format_with(&options).to_string())
}

/// Split a qualified function name, requiring both names to be present.
pub fn split_qualified_function_name(name: &str) -> Option<(&str, &str)> {
    name.rsplit_once("::")
        .filter(|(module, function)| !module.is_empty() && !function.is_empty())
}

/// Render a function by local name/index, qualified name, or name/index plus module.
pub fn function_text(
    session: &CompilerSession,
    current: ModuleId,
    function: &str,
    module: Option<&str>,
) -> Result<String, String> {
    let (module_name, function) = if module.is_some() {
        (module, function)
    } else if let Some((module, function)) = split_qualified_function_name(function) {
        (Some(module), function)
    } else {
        (None, function)
    };
    let id = selected_module(session, current, module_name)?;
    let module = session.modules().get(id).ok_or_else(|| {
        "Module never compiled successfully and is thus not available for inspection.".to_string()
    })?;
    let module_name = module_name.unwrap_or("current");
    let fn_id = match function.parse::<usize>() {
        Ok(index) => LocalFunctionId::from_index(index),
        Err(_) => module
            .get_local_function_id(ustr(function))
            .ok_or_else(|| {
                format!("Function name {function} not found in module {module_name}.")
            })?,
    };
    let function = module
        .get_function_by_id(fn_id)
        .ok_or_else(|| format!("Function id {fn_id} not found in module {module_name}."))?;
    let name = module
        .get_function_name_by_id(fn_id)
        .unwrap_or_else(|| ustr("<anonymous function>"));
    let env = session.modules().env_for(module);
    Ok((function, name).format_with(&env).to_string())
}

/// List the compiled submissions, using the same statistics in either frontend.
pub fn history_text(session: &CompilerSession, counter: usize) -> String {
    (0..counter)
        .filter_map(|index| {
            let name = format!("repl{index}");
            session
                .modules()
                .get_by_path(&Path::single_str(&name))
                .map(|(_, module)| format!("{name}: {}", module.list_stats()))
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Render physical MIR without exposing compiler-internal source map APIs to frontends.
pub fn physical_mir_text(session: &CompilerSession, module: ModuleId) -> Result<String, String> {
    session
        .emit_physical_mir_module_with_source_map(module)
        .map(|text| text.text)
        .map_err(|error| {
            error
                .format_with(&(session.source_table(), session.modules()))
                .to_string()
        })
}

/// The same console contract on native and Wasm hosts; only the output callback differs.
pub fn console_module(module_id: ModuleId, print: extern "C" fn(&FerliumString)) -> Module {
    let mut module = new_module_using_std(module_id, Path::single_str("console"));
    module.add_function(
        ustr("print"),
        NativeFnR::new(print).description(
            ["message"],
            "Prints `message` to the REPL console.",
            effect_write(),
        ),
    );
    module
}
