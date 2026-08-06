// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::fmt;

use crate::{
    containers::B,
    format::FormatWith,
    hir::value::LiteralValue,
    module::{FunctionId, ModuleEnv, QualifiedNameEnv, SubscriptId, TraitDictionaryId, id::Id},
    types::r#type::Type,
};

/// A value in the MIR form of Ferlium.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Value {
    /// A typed opaque HIR immediate in the containing function's constant pool.
    Constant(ConstantId),

    /// A symbolic trait dictionary, identified by the canonical handle of the impl that satisfies
    /// it. The dictionary is kept symbolic (an interned id) rather than materialized into a tuple
    /// of trait-function values (including associated-constant getters); the MIR interpreter
    /// dispatches through the interned id, and a later tuple-lowering pass (for a real
    /// backend) rebuilds the witness table from the impl arena. A *forwarded* dictionary (one a
    /// generic function received as an extra parameter) is instead represented by its `Parameter`.
    Dictionary(TraitDictionaryId),

    /// A symbolic first-class subscript (projection evidence), identified by the id of the
    /// subscript it references. Like a dictionary it is kept symbolic rather than materialized: the
    /// MIR interpreter resolves members through it via `subscript_member`, and a later lowering
    /// pass (for a real backend) materializes it as a member-table value. A *forwarded* subscript
    /// (one a generic function received as an extra parameter) is instead represented by the
    /// `Parameter` slot it arrives in, not by this variant.
    Subscript(SubscriptId),

    /// A reference to a lowered function.
    Function(FunctionId),

    /// A parameter in the containing function's signature.
    Parameter(ParameterId),

    /// A function-local result value defined by an operation.
    Register(ValueId),

    /// Compile-time pattern data used only by a `comp_eq` operation.
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
            Value::Register(i) => write!(f, "%r{}", i.as_index()),
            Value::Pattern(lit) => write!(f, "{}", lit),
        }
    }
}

crate::define_id_type!(
    /// The stable identity of a typed immediate in a MIR function's constant pool.
    ConstantId
);

crate::define_id_type!(
    /// The stable identity of a parameter in a MIR function's signature.
    ParameterId
);

crate::define_id_type!(
    /// The stable identity of an operation result within a MIR function.
    ValueId
);

/// A typed, trivially-copyable HIR immediate representation.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Constant {
    pub ty: Type,
    pub representation: LiteralValue,
}

impl FormatWith<ModuleEnv<'_>> for Value {
    fn fmt_with(&self, f: &mut fmt::Formatter<'_>, env: &ModuleEnv<'_>) -> fmt::Result {
        match self {
            Value::Dictionary(id) => {
                let Some(module) = env.module_by_id(id.module_id) else {
                    return fmt::Display::fmt(self, f);
                };
                let Some(key) = module.get_impl_trait_key_by_id(id.impl_id) else {
                    return fmt::Display::fmt(self, f);
                };
                let trait_def = env.trait_def(key.trait_id());
                let qualified_names = QualifiedNameEnv::new_from_module(module, env.modules);
                write!(
                    f,
                    "dict({})",
                    qualified_names.qualified_impl_name(key.trait_id(), trait_def, key.input_tys())
                )
            }
            Value::Function(id) => {
                let module = env
                    .module_by_id(id.module)
                    .expect("MIR function operand refers to an unavailable module");
                let function = module
                    .get_function_name_by_id(id.function)
                    // A specialization has no entry in the function table, so its generated name
                    // comes from the artifacts that hold it. Without this a call to one renders as
                    // `<anonymous>`, which is exactly where a reader most needs to be told which
                    // original and which instantiation they are looking at.
                    .or_else(|| env.specialization_name(*id))
                    .unwrap_or_else(|| "<anonymous>".into());
                let module_name = env
                    .modules
                    .get_name(id.module)
                    .map(ToString::to_string)
                    .unwrap_or_else(|| format!("#{}", id.module));
                write!(f, "{module_name}::{function}")
            }
            _ => fmt::Display::fmt(self, f),
        }
    }
}
