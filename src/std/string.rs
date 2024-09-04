use std::{fmt, fmt::Display, rc::Rc, str::FromStr};

use ustr::ustr;

use crate::{
    function::{BinaryNativeFnMNI, BinaryNativeFnNNI, UnaryNativeFnNI, UnaryNativeFnVI},
    module::Module,
    r#type::Type,
    value::{NativeDisplay, Value},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct String(Rc<std::string::String>);

impl String {
    pub fn new() -> Self {
        Self(Rc::new(std::string::String::new()))
    }

    pub fn any_to_string(value: Value) -> Self {
        struct FormatInToString<'a>(pub &'a Value);
        impl fmt::Display for FormatInToString<'_> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                self.0.format_as_string(f)
            }
        }
        let string = format!("{}", FormatInToString(&value));
        Self(Rc::new(string))
    }

    pub fn push_str(&mut self, value: Self) {
        Rc::make_mut(&mut self.0).push_str(value.0.as_str());
    }

    pub fn concat(l: &Self, r: &Self) -> Self {
        let mut new = l.clone();
        new.push_str(r.clone());
        new
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl FromStr for String {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self(Rc::new(s.to_string())))
    }
}

impl AsRef<str> for String {
    fn as_ref(&self) -> &str {
        self.0.as_str()
    }
}

impl Display for String {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Default for String {
    fn default() -> Self {
        Self::new()
    }
}

impl NativeDisplay for String {
    fn fmt_as_literal(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\"{}\"", self.0)
    }
    fn fmt_in_to_string(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

pub fn string_type() -> Type {
    Type::primitive::<String>()
}

pub fn add_to_module(to: &mut Module) {
    to.types.set(ustr("string"), string_type());

    to.functions.insert(
        ustr("to_string"),
        UnaryNativeFnVI::description_with_default_ty(String::any_to_string),
    );
    to.functions.insert(
        ustr("string_push_str"),
        BinaryNativeFnMNI::description_with_default_ty(String::push_str),
    );
    to.functions.insert(
        ustr("string_concat"),
        BinaryNativeFnNNI::description_with_default_ty(|a: String, b: String| {
            String::concat(&a, &b)
        }),
    );
    to.functions.insert(
        ustr("string_len"),
        UnaryNativeFnNI::description_with_default_ty(|a: String| a.len() as isize),
    );
    to.functions.insert(
        ustr("string_is_empty"),
        UnaryNativeFnNI::description_with_default_ty(|a: String| a.is_empty() as isize),
    );
}
