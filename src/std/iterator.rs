use crate::r#type::Type;

use super::option::option_type;

// Note: not used currently until we have algebraic data types in the compiler
pub fn iterator_type() -> Type {
    Type::function_by_val(&[], Type::tuple(vec![option_type(), Type::new_local(0)]))
}
