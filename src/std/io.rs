use crate::{function::UnaryNativeFnVI, module::Module, r#type::Type, value::Value};

use ustr::ustr;

fn log(value: Value) {
    log::info!("{}", value);
}

pub fn add_to_module(to: &mut Module) {
    to.functions.insert(
        ustr("log"),
        UnaryNativeFnVI::description_with_ty(log, Type::variable_id(0)),
    );
}
