use std::{fmt, rc::Rc};

use ustr::ustr;

use crate::{module::Module, r#type::Type, value::NativeDisplay};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct String(Rc<std::string::String>);

impl String {
    pub fn new() -> Self {
        Self(Rc::new(std::string::String::new()))
    }

    fn append(&mut self, value: Self) {
        Rc::make_mut(&mut self.0).push_str(value.0.as_str());
    }

    fn concat(l: &Self, r: &Self) -> Self {
        let mut new = l.clone();
        new.append(r.clone());
        new
    }
}

impl Default for String {
    fn default() -> Self {
        Self::new()
    }
}

impl NativeDisplay for String {
    fn native_fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\"{}\"", self.0)
    }
}

pub fn string_type() -> Type {
    Type::primitive::<String>()
}

pub fn add_to_module(to: &mut Module) {
    to.types.set(ustr("string"), string_type());
}
