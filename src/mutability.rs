use std::fmt::Display;

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
