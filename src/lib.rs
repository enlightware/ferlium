// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

pub use rustc_hash::{FxHashMap, FxHashSet};
pub use ustr::{Ustr, ustr};

mod assert;
pub mod compiler;
pub mod containers;
mod desugar;
pub mod eval;
pub mod format;
mod graph;
pub mod hir;
pub mod ide;
pub mod module;
pub mod parser;
pub mod std;
mod sync;
pub mod types;

pub use compiler::error::{CompilationError, LocatedError};
pub use compiler::{CompilerSession, ModuleAndExpr, Modules, parse_module_and_expr};
pub(crate) use compiler::{EvalExprError, add_code_to_module};
pub use ide::Compiler;
pub use module::{ModuleEnv, Path};
pub use parser::location::{Location, SourceId, SourceTable};
pub use types::type_inference::unify::SubOrSameType;

use types::type_scheme::DisplayStyle;

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
                $( $crate::types::r#type::FnArgType::new_by_val($ty) ),*
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
            [ $( $crate::hir::value::Value::native($val.clone()) => $crate::types::r#type::Type::primitive::<$ty>() ),* ]
            -> $crate::types::r#type::Type::unit()
        ).map(|_| ())
    };
    // Primitive return
    ( $session:expr, $module_id:expr, $name:expr, [ $( $val:expr => $ty:ty ),* $(,)? ] -> $ret:ty ) => {
        $crate::call_fn!(
            $session, $module_id, $name,
            [ $( $crate::hir::value::Value::native($val.clone()) => $crate::types::r#type::Type::primitive::<$ty>() ),* ]
            -> $crate::types::r#type::Type::primitive::<$ret>()
        ).map(|ret| ret.into_primitive_ty::<$ret>().unwrap())
    };
}
