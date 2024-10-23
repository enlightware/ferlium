use ustr::ustr;

use crate::{
    effects::no_effects,
    error::RuntimeError,
    function::NullaryNativeFnFN,
    module::Module,
    r#type::{FnType, Type},
    type_scheme::TypeScheme,
};

fn abort() -> Result<(), RuntimeError> {
    Err(RuntimeError::Aborted)
}

pub fn add_to_module(to: &mut Module) {
    // Control flow operation
    // Note: we use no_effects() for now as non-termination is modelled purely in the return type
    to.functions.insert(
        ustr("abort"),
        NullaryNativeFnFN::description_with_ty_scheme(
            abort,
            TypeScheme::new_just_type(FnType::new_by_val(&[], Type::never(), no_effects())),
        ),
    );
}
