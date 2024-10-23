use crate::r#type::Type;
use ustr::ustr;

pub fn option_type(inner: Type) -> Type {
    Type::variant(vec![(ustr("None"), Type::unit()), (ustr("Some"), inner)])
}

pub fn gen_option_type() -> Type {
    option_type(Type::variable_id(0))
}
