use std::fmt;

use crate::{
    containers::B,
    format::FormatWith,
    hir::value::LiteralValue,
    module::{FunctionId, ModuleEnv, SubscriptId, TraitDictionaryId},
    ssa,
    types::r#type::Type,
};

/// A value in the SSA form of Ferlium.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Value {
    /// A typed opaque HIR immediate in the containing function's constant pool.
    Constant(ConstantId),

    /// A symbolic trait dictionary, identified by the canonical handle of the impl that satisfies
    /// it. The dictionary is kept symbolic (an interned id) rather than materialized into a tuple
    /// of trait-function values (including associated-constant getters); the SSA interpreter
    /// dispatches through it via `DictArg::Interned`, and a later tuple-lowering pass (for a real
    /// backend) rebuilds the witness table from the impl arena. A *forwarded* dictionary (one a
    /// generic function received as an extra parameter) is instead represented by its `Parameter`.
    Dictionary(TraitDictionaryId),

    /// A symbolic first-class subscript (projection evidence), identified by the id of the
    /// subscript it references. Like a dictionary it is kept symbolic rather than materialized: the
    /// SSA interpreter resolves members through it via `subscript_member`, and a later lowering
    /// pass (for a real backend) materializes it as a member-table value. A *forwarded* subscript
    /// (one a generic function received as an extra parameter) is instead represented by the
    /// `Parameter` slot it arrives in, not by this variant.
    Subscript(SubscriptId),

    /// A reference to a lowered function.
    Function(FunctionId),

    /// The `i`-th parameter of a function.
    Parameter(usize),

    /// The register assigned by an instruction.
    Register(ssa::InstructionIdentity),

    /// Compile-time pattern data used only by a `comp_eq` instruction.
    Pattern(B<LiteralValue>),
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Constant(id) => write!(f, "@c{}", id.as_index()),
            Value::Dictionary(id) => {
                write!(f, "dict(m{}:i{})", id.module_id, id.impl_id)
            }
            Value::Subscript(id) => {
                write!(f, "subscript(m{}:s{})", id.module, id.subscript)
            }
            Value::Function(id) => write!(f, "fn(m{}:f{})", id.module, id.function),
            Value::Parameter(i) => write!(f, "%p{}", i),
            Value::Register(i) => write!(f, "%r{}", i.raw()),
            Value::Pattern(lit) => write!(f, "{}", lit),
        }
    }
}

/// The stable identity of a typed immediate in an SSA function's constant pool.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ConstantId(usize);

impl ConstantId {
    pub(crate) fn from_index(index: usize) -> Self {
        Self(index)
    }

    pub fn as_index(self) -> usize {
        self.0
    }
}

/// A typed, trivially-copyable HIR immediate representation.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Constant {
    pub ty: Type,
    pub representation: LiteralValue,
}

impl FormatWith<ModuleEnv<'_>> for Value {
    fn fmt_with(&self, f: &mut fmt::Formatter<'_>, env: &ModuleEnv<'_>) -> fmt::Result {
        let Value::Function(id) = self else {
            return fmt::Display::fmt(self, f);
        };
        let module = if id.module == env.current.module_id() {
            env.current
        } else {
            env.modules
                .get(id.module)
                .and_then(|entry| entry.module.as_ref())
                .expect("SSA function operand refers to an unavailable module")
        };
        let function = module
            .get_function_name_by_id(id.function)
            .unwrap_or_else(|| "<anonymous>".into());
        let module_name = env
            .modules
            .get_name(id.module)
            .map(ToString::to_string)
            .unwrap_or_else(|| format!("#{}", id.module));
        write!(f, "{module_name}::{function}")
    }
}
