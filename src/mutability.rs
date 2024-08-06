use std::fmt::{self, Display};

use enum_as_inner::EnumAsInner;

use crate::format::type_variable_index_to_string;

/// A mutability value, newtype because we must implement EqUnifyValue for it
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MutVal(bool);
impl MutVal {
    pub fn mutable() -> Self {
        Self(true)
    }
    pub fn constant() -> Self {
        Self(false)
    }
    pub fn is_mutable(&self) -> bool {
        self.0
    }
    pub fn var_def_string(&self) -> &'static str {
        ["let", "var"][self.0 as usize]
    }
}

impl From<bool> for MutVal {
    fn from(b: bool) -> Self {
        Self(b)
    }
}

impl From<MutVal> for bool {
    fn from(m: MutVal) -> Self {
        m.0
    }
}
impl From<&MutVal> for bool {
    fn from(m: &MutVal) -> Self {
        m.0
    }
}

impl Display for MutVal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", ["cst", "mut"][self.0 as usize])
    }
}

/// A mutability variable, used to infer whether a variable is mutable or not
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MutVar(pub(crate) u32);

impl Display for MutVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}ₘ", type_variable_index_to_string(self.0))
    }
}

/// A mutability type, can be a variable or a resolved value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, EnumAsInner)]
pub enum MutType {
    Variable(MutVar),
    Resolved(MutVal),
}
impl MutType {
    pub fn mutable() -> Self {
        Self::resolved(MutVal::mutable())
    }
    pub fn constant() -> Self {
        Self::resolved(MutVal::constant())
    }
    pub fn resolved(value: MutVal) -> Self {
        MutType::Resolved(value)
    }
    pub fn variable(var: MutVar) -> Self {
        MutType::Variable(var)
    }

    pub fn is_mutable(&self) -> bool {
        match self {
            MutType::Variable(_) => false,
            MutType::Resolved(val) => val.is_mutable(),
        }
    }

    pub fn format_in_fn_arg(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            MutType::Variable(var) => write!(f, "inout?:{} ", var),
            MutType::Resolved(val) => {
                if val.is_mutable() {
                    write!(f, "inout ")
                } else {
                    Ok(())
                }
            }
        }
    }
}

impl From<bool> for MutType {
    fn from(b: bool) -> Self {
        Self::resolved(b.into())
    }
}

impl Display for MutType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use MutType::*;
        match self {
            Variable(var) => write!(f, "mut?:{}", var),
            Resolved(val) => write!(f, "{}", val),
        }
    }
}
