use crate::{function::UnaryNativeFnVP, module::Module, value::Value};

use ustr::ustr;

fn log(value: &Value) {
    log::info!("{}", value);
}

pub fn add_to_module(to: &mut Module) {
    to.functions.insert(
        ustr("log"),
        UnaryNativeFnVP::description(log),
    );
}