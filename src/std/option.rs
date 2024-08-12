use crate::r#type::Type;
use ustr::ustr;

// Note: not used currently until we have algebraic data types in the compiler
pub fn option_type() -> Type {
    let gen0 = Type::variable_id(0);
    Type::variant(vec![(ustr("None"), Type::unit()), (ustr("Some"), gen0)])
}
