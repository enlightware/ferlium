use std::{rc::Rc, str::FromStr};

use crate::{
    module::{Module, Modules, Use},
    r#type::{bare_native_type, Type, TypeKind},
    value::Value,
};

use array::Array;
use math::{Float, Int};
use ustr::ustr;

pub mod array;
pub mod flow;
pub mod io;
pub mod iterator;
pub mod logic;
pub mod math;
pub mod mem;
pub mod option;
pub mod range;
pub mod string;

pub fn std_module() -> Module {
    let mut module = Module::default();
    module.types.set(ustr("()"), Type::unit());
    flow::add_to_module(&mut module);
    // mem::add_to_module(&mut module);
    logic::add_to_module(&mut module);
    math::add_to_module(&mut module);
    range::add_to_module(&mut module);
    array::add_to_module(&mut module);
    io::add_to_module(&mut module);
    string::add_to_module(&mut module);
    // option::add_option_functions(&mut module);
    module
}

pub fn new_std_module_env() -> Modules {
    let mut modules: Modules = Default::default();
    modules.insert(ustr("std"), Rc::new(std_module()));
    modules
}

pub fn new_module_with_prelude() -> Module {
    let mut new_module = Module::default();
    new_module.uses.push(Use::All(ustr("std")));
    new_module
}

pub fn default_value_for_type(ty: Type) -> Option<Value> {
    use TypeKind::*;
    match &*ty.data() {
        Variable(_) => None,
        Native(native_type) => {
            if native_type.bare_ty == bare_native_type::<()>() {
                Some(Value::unit())
            } else if native_type.bare_ty == bare_native_type::<bool>() {
                Some(Value::native(false))
            } else if native_type.bare_ty == bare_native_type::<Int>() {
                Some(Value::native(0))
            } else if native_type.bare_ty == bare_native_type::<Float>() {
                Some(Value::native::<Float>(Float::new(0.0).unwrap()))
            } else if native_type.bare_ty == bare_native_type::<string::String>() {
                Some(Value::native(string::String::from_str("").unwrap()))
            } else if native_type.bare_ty == bare_native_type::<Array>() {
                Some(Value::native(Array::new()))
            } else {
                None
            }
        }
        Tuple(tys) => tys
            .iter()
            .map(|ty| default_value_for_type(*ty))
            .collect::<Option<Vec<_>>>()
            .map(Value::tuple),
        Record(fields) => fields
            .iter()
            .map(|(_, ty)| default_value_for_type(*ty))
            .collect::<Option<Vec<_>>>()
            .map(Value::tuple),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;
    use ustr::ustr;

    use ordered_float::NotNan;

    use crate::{
        r#type::Type,
        std::{
            array::{array_type, Array},
            logic::bool_type,
            math::{float_type, int_type},
            string::{self, string_type},
        },
        value::Value,
    };

    #[test]
    fn default_value_for_type() {
        use super::default_value_for_type as def_val;
        assert_eq!(def_val(Type::unit()), Some(Value::unit()));
        assert_eq!(def_val(bool_type()), Some(Value::native(false)));
        assert_eq!(def_val(int_type()), Some(Value::native(0_isize)));
        assert_eq!(
            def_val(float_type()),
            Some(Value::native(NotNan::new(0.0_f64).unwrap()))
        );
        assert_eq!(
            def_val(string_type()),
            Some(Value::native(string::String::from_str("").unwrap()))
        );
        assert_eq!(
            def_val(array_type(int_type())),
            Some(Value::native(Array::new()))
        );
        assert_eq!(
            def_val(array_type(float_type())),
            Some(Value::native(Array::new()))
        );
        assert_eq!(
            def_val(Type::tuple(vec![int_type(), bool_type()])),
            Some(Value::tuple(vec![
                Value::native(0_isize),
                Value::native(false)
            ]))
        );
        assert_eq!(
            def_val(Type::record(vec![
                (ustr("a"), int_type()),
                (ustr("b"), bool_type())
            ])),
            Some(Value::tuple(vec![
                Value::native(0_isize),
                Value::native(false)
            ]))
        );
    }
}
