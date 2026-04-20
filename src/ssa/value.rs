use std::fmt;

use itertools::Itertools;
use ustr::Ustr;

use crate::ssa;

/// A value in the SSA form of Ferlium.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Value {
  /// The `i`-th parameter of a function.
  Parameter(usize),

  /// The register assigned by an instruction.
  Register(ssa::InstructionIdentity),

  /// A unit value.
  Unit,

  /// A constant boolean
  Boolean(bool),

  /// A constant integer.
  Integer(Box<Integer>),

  /// A reference to a lowered function.
  Function(Ustr),

  /// A reference to a dict
  Dictionary(Vec<ssa::Value>),
}

impl fmt::Display for Value {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Value::Parameter(i) => write!(f, "%p{}", i),
      Value::Register(i) => write!(f, "%r{}", i.raw()),
      Value::Unit => write!(f, "()"),
      Value::Boolean(i) => write!(f, "i1 {}", *i as u8),
      Value::Integer(i) => i.fmt(f),
      Value::Function(i) => i.fmt(f),
      Value::Dictionary(i) => {
        write!(f, "({})", i.iter().map(|v| format!("{}", v)).join(", "))
      }
    }
  }
}

/// A constant integer, represented as a two's complement value.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Integer {
  /// The bit pattern of the value. Only the `bit_width` least significant bits are relevant.
  pub bits: u64,

  /// The number of bits in the representation of `self`.
  pub bit_width: u8,

  /// `true` iff the representation of `self` is signed.
  pub signed: bool,
}

impl Integer {
  pub fn from_isize(value: isize) -> Self {
    Self {
      bits: isize::cast_unsigned(value) as u64,
      bit_width: 32,
      signed: true,
    }
  }

  pub fn from_u32(value: u32) -> Self {
    Self {
      bits: value.into(),
      bit_width: 32,
      signed: false,
    }
  }

  pub fn from_i32(value: i32) -> Self {
    Self {
      bits: i32::cast_unsigned(value).into(),
      bit_width: 32,
      signed: true,
    }
  }
}

impl fmt::Display for Integer {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    if self.signed {
      write!(f, "i{} {}", self.bit_width, u64::cast_signed(self.bits))
    } else {
      write!(f, "u{} {}", self.bit_width, self.bits)
    }
  }
}
