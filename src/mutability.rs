// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::fmt::{self, Display};

use derive_new::new;
use enum_as_inner::EnumAsInner;

use crate::format::type_variable_index_to_string_greek;

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

/// A generic variable for mutability
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, new)]
pub struct MutVar {
    /// The name of this mutability variable, its identity in the context considered
    name: u32,
}

impl MutVar {
    pub fn name(&self) -> u32 {
        self.name
    }
}

impl Display for MutVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}ₘ", type_variable_index_to_string_greek(self.name))
    }
}

pub type MutVarKey = MutVar;

pub trait FormatInFnArg {
    fn format_in_fn_arg(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result;
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
    pub fn variable_id(id: u32) -> Self {
        MutType::Variable(MutVar::new(id))
    }

    pub fn is_mutable(&self) -> bool {
        match self {
            MutType::Variable(_) => false,
            MutType::Resolved(val) => val.is_mutable(),
        }
    }
}

impl FormatInFnArg for MutType {
    fn format_in_fn_arg(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use MutType::*;
        match self {
            Variable(var) => write!(f, "&{var} "),
            Resolved(val) => {
                if val.is_mutable() {
                    write!(f, "&mut ")
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
            Variable(var) => write!(f, "mut?:{var}"),
            Resolved(val) => write!(f, "{val}"),
        }
    }
}
