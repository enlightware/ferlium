use crate::{r#type::Type, value::Value};
use ustr::ustr;

pub fn option_type(inner: Type) -> Type {
    Type::variant(vec![(ustr("None"), Type::unit()), (ustr("Some"), inner)])
}

pub fn gen_option_type() -> Type {
    option_type(Type::variable_id(0))
}

pub fn none() -> Value {
    Value::variant(ustr("None"), Value::unit())
}

pub fn some(value: Value) -> Value {
    Value::variant(ustr("Some"), value)
}
