// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Check bounded result reconstruction before lowering final HIR.

use crate::{
    FxHashSet, compiler::error::CompilerLimit, mir::results::check_result_limits, module::ModuleEnv,
};

pub(crate) fn check_module_result_limits(env: ModuleEnv<'_>) -> Result<(), CompilerLimit> {
    let mut checked = FxHashSet::default();
    for function in env.current.iter_functions() {
        if let Some(script) = function.code.as_script() {
            let span = env.current.hir_arena[script.entry_node_id].span;
            let ty = function.definition.ty_scheme.ty.ret;
            if checked.insert(ty) {
                check_result_limits(ty, &env, span)?;
            }
        }
    }
    for (_, node) in env.current.hir_arena.iter() {
        if checked.insert(node.ty) {
            check_result_limits(node.ty, &env, node.span)?;
        }
    }
    Ok(())
}
