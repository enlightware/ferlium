use crate::r#type::Type;
use ustr::ustr;

pub fn option_type() -> Type {
    let gen0 = Type::variable_id(0);
    Type::variant(vec![(ustr("None"), Type::unit()), (ustr("Some"), gen0)])
}
