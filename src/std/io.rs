// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::sync::{LazyLock, RwLock};

use crate::{
    effects::{PrimitiveEffect, effect},
    function::UnaryNativeFnVN,
    module::Module,
    r#type::Type,
    value::Value,
};

use ustr::ustr;

static LOG_CTX: LazyLock<RwLock<String>> = LazyLock::new(|| RwLock::new(String::new()));

pub fn set_log_ctx(new_ctx: &str) {
    let mut ctx = LOG_CTX.write().unwrap();
    *ctx = new_ctx.to_string();
}

fn log(value: Value) {
    let ctx = (*LOG_CTX).read().unwrap();
    log::info!("{}{}", *ctx, value.to_string_repr());
}

pub fn add_to_module(to: &mut Module) {
    to.add_function(
        ustr("log"),
        UnaryNativeFnVN::description_with_in_ty(
            log,
            ["message"],
            "Logs a message to the standard logging output.",
            Type::variable_id(0),
            effect(PrimitiveEffect::Write),
        ),
    );
}
