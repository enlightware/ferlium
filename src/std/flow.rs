use ustr::ustr;

use crate::{
    error::RuntimeError,
    function::NullaryNativeFnF,
    module::Module,
    r#type::{FnType, Type},
    type_scheme::TypeScheme,
};

fn abort() -> Result<(), RuntimeError> {
    Err(RuntimeError::Aborted)
}

pub fn add_to_module(to: &mut Module) {
    // Control flow operation
    to.functions.insert(
        ustr("abort"),
        NullaryNativeFnF::description_with_ty_scheme(
            abort,
            TypeScheme::new_just_type(FnType::new_by_val(&[], Type::never())),
        ),
    );
}
