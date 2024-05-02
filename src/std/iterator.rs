use crate::r#type::Type;

use super::option::option_type;

pub fn iterator_type() -> Type {
    Type::function(&[], Type::tuple(vec![option_type(), Type::new_local(0)]))
}
