use std::sync::{LazyLock, RwLock};

use crate::{
    effects::{effect, PrimitiveEffect},
    function::UnaryNativeFnVI,
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
    log::info!("{}{}", *ctx, value);
}

pub fn add_to_module(to: &mut Module) {
    to.functions.insert(
        ustr("log"),
        UnaryNativeFnVI::description_with_ty(
            log,
            Type::variable_id(0),
            effect(PrimitiveEffect::Write),
        ),
    );
}
