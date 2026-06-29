use std::fmt;

use ordered_float::NotNan;
use ustr::Ustr;

use crate::types::r#type::Type;
use crate::{
    module::{LocalFunctionId, ModuleId, TraitDictionaryId},
    ssa,
};

/// A value in the SSA form of Ferlium.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Value {
    /// A constant boolean
    Boolean(bool),

    /// A symbolic trait dictionary, identified by the canonical handle of the impl that satisfies
    /// it. The dictionary is kept symbolic (an interned id) rather than materialized into a tuple of
    /// method function values and associated consts; the SSA interpreter dispatches through it via
    /// `DictArg::Interned`, and a later tuple-lowering pass (for a real backend) rebuilds the witness
    /// table from the impl arena exactly as `Emitter::lower_dictionary` did. A *forwarded* dictionary
    /// (one a generic function received as an extra parameter) is instead represented by the
    /// `Parameter` slot it arrives in, not by this variant.
    Dictionary(TraitDictionaryId),

    /// A constant finite float (`float`), represented as an `f64` that is never NaN.
    Float(NotNan<f64>),

    /// A reference to a lowered function.
    Function(FunctionReference),

    /// A constant integer.
    Integer(Box<Integer>),

    /// The `i`-th parameter of a function.
    Parameter(usize),

    /// The register assigned by an instruction.
    Register(ssa::InstructionIdentity),

    /// A unit value.
    Unit,

    /// A constant string value.
    String(crate::std::string::String),

    /// A constant literal value (a scalar or a composite tuple/record), used as a `match` pattern.
    /// Scalars also have dedicated variants above; this carries whole composite patterns — e.g.
    /// `(true, true)` — that have no single scalar form, so a `match` can compare the whole scrutinee
    /// against the whole pattern structurally (mirroring the HIR interpreter's `LiteralValue`
    /// equality) instead of decomposing it.
    Literal(crate::containers::B<crate::hir::value::LiteralValue>),

    /// An uninitialized value of type `T`.
    Uninit(ShownType),
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Boolean(i) => write!(f, "i1 {}", *i as u8),
            Value::Dictionary(id) => {
                write!(f, "dict(m{}:i{})", id.module_id, id.impl_id)
            }
            Value::Float(x) => write!(f, "float {}", x.into_inner()),
            Value::Function(i) => write!(f, "{}", i.name),
            Value::Integer(i) => i.fmt(f),
            Value::Parameter(i) => write!(f, "%p{}", i),
            Value::Register(i) => write!(f, "%r{}", i.raw()),
            Value::Unit => write!(f, "()"),
            Value::Uninit(t) => write!(f, "Uninit<{}>", t.name),
            Value::String(s) => write!(f, "\"{}\"", s),
            Value::Literal(lit) => write!(f, "{}", lit),
        }
    }
}

/// A function reference, represented as its reference, and its representation
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct FunctionReference {
    /// The qualified name of `self`.
    pub name: Ustr,

    /// The module id in which the function is defined.
    pub module: ModuleId,

    /// The LocalFunctionId in the module in which the function is declared.
    pub identity: LocalFunctionId,
}

/// A type identity along with the type's string representation.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct ShownType {
    /// The type's identity.
    pub ty: Type,

    /// The string representation of `ty`.
    pub name: String,
}

/// The width of an SSA integer constant.
///
/// Keeping the pointer-sized case symbolic (rather than baking in 32 or 64) makes the SSA IR target
/// independent: `PointerSized` represents `int`/`isize`/`usize`, whose physical width is resolved by
/// the backend profile (see `doc/abi.md`).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum IntWidth {
    /// A fixed bit width, e.g. `i8`, `i32`, `u64`.
    FixedSize(i16),

    /// A pointer-sized width (`int`/`isize`/`usize`), resolved per backend profile.
    PointerSized,
}

/// A constant integer, represented as a two's complement value.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Integer {
    /// The bit pattern of the value. Only the `width` least significant bits are relevant.
    pub bits: u64,

    /// The width of the representation of `self`.
    pub width: IntWidth,

    /// `true` iff the representation of `self` is signed.
    pub signed: bool,
}

impl Integer {
    pub fn from_isize(value: isize) -> Self {
        Self {
            bits: isize::cast_unsigned(value) as u64,
            width: IntWidth::PointerSized,
            signed: true,
        }
    }

    pub fn from_u32(value: u32) -> Self {
        Self {
            bits: value.into(),
            width: IntWidth::FixedSize(32),
            signed: false,
        }
    }

    pub fn from_i32(value: i32) -> Self {
        Self {
            bits: i32::cast_unsigned(value).into(),
            width: IntWidth::FixedSize(32),
            signed: true,
        }
    }

    /// Interprets `self` as a two's-complement integer and returns its value as an `isize`.
    ///
    /// Only the low `width` bits of `bits` are significant; a signed value is sign-extended from
    /// that width. This is the bridge used by the SSA interpreter, which represents every integer
    /// as the host `isize` (matching the HIR runtime representation of `int`).
    pub fn to_isize(&self) -> isize {
        match self.width {
            IntWidth::PointerSized => self.bits as i64 as isize,
            IntWidth::FixedSize(w) => {
                let w = w as u32;
                if self.signed && w < 64 {
                    let shift = 64 - w;
                    (((self.bits << shift) as i64) >> shift) as isize
                } else {
                    self.bits as isize
                }
            }
        }
    }
}

impl fmt::Display for Integer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.width {
            IntWidth::FixedSize(bits) => {
                if self.signed {
                    write!(f, "i{} {}", bits, u64::cast_signed(self.bits))
                } else {
                    write!(f, "u{} {}", bits, self.bits)
                }
            }
            IntWidth::PointerSized => {
                if self.signed {
                    write!(f, "int {}", u64::cast_signed(self.bits))
                } else {
                    write!(f, "uint {}", self.bits)
                }
            }
        }
    }
}
