// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use std::{
    fmt,
    hash::{Hash, Hasher},
    mem::discriminant,
};

use crate::{
    containers::B,
    define_id_type,
    format::FormatWith,
    hir::value::LiteralValue,
    module::{FunctionId, ModuleEnv, QualifiedNameEnv, SubscriptId, TraitDictionaryId, id::Id},
    std::math::Float,
    types::r#type::Type,
};

/// A value in the MIR form of Ferlium.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Value {
    /// A typed opaque HIR immediate in the containing function's constant pool.
    Constant(ConstantId),

    /// A symbolic trait dictionary, identified by the canonical handle of the impl that satisfies
    /// it. The MIR interpreters dispatch through the id. A physical module carries relocatable
    /// metadata for its definitions and imports, from which whole-program assembly selects the
    /// target representation. A *forwarded* dictionary received as an extra parameter is instead
    /// represented by its `Parameter`.
    Dictionary(TraitDictionaryId),

    /// A symbolic first-class subscript (projection evidence), identified by the id of the
    /// subscript it references. Like a dictionary it is kept symbolic rather than materialized: the
    /// MIR interpreter resolves members through it via `subscript_member`. Physical modules carry
    /// the definition in a relocatable catalog which whole-program assembly resolves alongside
    /// dictionaries. A *forwarded* subscript received as an extra parameter is instead represented
    /// by the `Parameter` slot it arrives in, not by this variant.
    Subscript(SubscriptId),

    /// Recursively static hidden evidence, including closed dictionaries with captures.
    Evidence(B<StaticEvidence>),

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
            Value::Evidence(evidence) => write!(f, "{evidence}"),
            Value::Function(id) => write!(f, "fn(m{}:f{})", id.module, id.function),
            Value::Parameter(i) => write!(f, "%p{}", i),
            Value::Register(i) => write!(f, "%r{}", i.as_index()),
            Value::Pattern(lit) => write!(f, "{}", lit),
        }
    }
}

/// Hashable compile-time form of closed hidden evidence.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum StaticEvidence {
    Dictionary {
        definition: TraitDictionaryId,
        captures: B<[StaticEvidence]>,
    },
    Subscript {
        definition: SubscriptId,
        captures: B<[StaticEvidence]>,
    },
    VariantPayloadStorage(bool),
}

impl StaticEvidence {
    pub fn bare_dictionary(definition: TraitDictionaryId) -> Self {
        Self::Dictionary {
            definition,
            captures: Box::new([]),
        }
    }

    pub fn bare_subscript(definition: SubscriptId) -> Self {
        Self::Subscript {
            definition,
            captures: Box::new([]),
        }
    }
}

impl fmt::Display for StaticEvidence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Dictionary {
                definition,
                captures,
            } => write!(
                f,
                "dict(m{}:i{}; {} captures)",
                definition.module_id,
                definition.impl_id,
                captures.len()
            ),
            Self::Subscript {
                definition,
                captures,
            } => write!(
                f,
                "subscript(m{}:s{}; {} captures)",
                definition.module,
                definition.subscript,
                captures.len()
            ),
            Self::VariantPayloadStorage(indirect) => write!(f, "layout({indirect})"),
        }
    }
}

define_id_type!(
    /// The stable identity of a typed immediate in a MIR function's constant pool.
    ConstantId
);

define_id_type!(
    /// The stable identity of a parameter in a MIR function's signature.
    ParameterId
);

define_id_type!(
    /// The stable identity of an operation result within a MIR function.
    ValueId
);

/// A typed, trivially-copyable HIR immediate representation.
#[derive(Clone, Eq, Debug)]
pub struct Constant {
    pub ty: Type,
    pub representation: LiteralValue,
}

/// MIR constants compare by observable representation, rather than runtime numeric equality.
impl PartialEq for Constant {
    fn eq(&self, other: &Self) -> bool {
        self.ty == other.ty
            && same_literal_representation(&self.representation, &other.representation)
    }
}

impl Hash for Constant {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.ty.hash(state);
        hash_literal_representation(&self.representation, state);
    }
}

/// Representation equality for MIR constants and dataflow facts, rather than numeric equality.
/// Keep this match exhaustive: any future composite literal must compare its children recursively.
pub(crate) fn same_literal_representation(left: &LiteralValue, right: &LiteralValue) -> bool {
    match left {
        LiteralValue::Tuple(left) => {
            let LiteralValue::Tuple(right) = right else {
                return false;
            };
            left.len() == right.len()
                && left
                    .iter()
                    .zip(right.iter())
                    .all(|(left, right)| same_literal_representation(left, right))
        }
        LiteralValue::Native(_) => match (
            left.as_primitive_ty::<Float>(),
            right.as_primitive_ty::<Float>(),
        ) {
            (Some(left), Some(right)) => {
                left.into_inner().to_bits() == right.into_inner().to_bits()
            }
            _ => left == right,
        },
        LiteralValue::VariantTag(left) => {
            matches!(right, LiteralValue::VariantTag(right) if left == right)
        }
    }
}

fn hash_literal_representation<H: Hasher>(literal: &LiteralValue, state: &mut H) {
    discriminant(literal).hash(state);
    match literal {
        LiteralValue::Tuple(values) => {
            values.len().hash(state);
            for value in values.iter() {
                hash_literal_representation(value, state);
            }
        }
        LiteralValue::Native(value) => {
            if let Some(value) = literal.as_primitive_ty::<Float>() {
                value.into_inner().to_bits().hash(state);
            } else {
                value.hash(state);
            }
        }
        LiteralValue::VariantTag(tag) => tag.hash(state),
    }
}

impl FormatWith<ModuleEnv<'_>> for Value {
    fn fmt_with(&self, f: &mut fmt::Formatter<'_>, env: &ModuleEnv<'_>) -> fmt::Result {
        match self {
            Value::Dictionary(id) => {
                write!(f, "dict(")?;
                format_dictionary_definition(f, *id, env)?;
                write!(f, ")")
            }
            Value::Evidence(evidence) => format_static_evidence(f, evidence, env),
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
            Value::Subscript(id) => {
                write!(f, "subscript(")?;
                format_subscript_definition(f, *id, env)?;
                write!(f, ")")
            }
            _ => fmt::Display::fmt(self, f),
        }
    }
}

fn format_static_evidence(
    f: &mut fmt::Formatter<'_>,
    evidence: &StaticEvidence,
    env: &ModuleEnv<'_>,
) -> fmt::Result {
    match evidence {
        StaticEvidence::Dictionary {
            definition,
            captures,
        } => {
            write!(f, "dict(")?;
            format_dictionary_definition(f, *definition, env)?;
            format_evidence_captures(f, captures, env)?;
            write!(f, ")")
        }
        StaticEvidence::Subscript {
            definition,
            captures,
        } => {
            write!(f, "subscript(")?;
            format_subscript_definition(f, *definition, env)?;
            format_evidence_captures(f, captures, env)?;
            write!(f, ")")
        }
        StaticEvidence::VariantPayloadStorage(indirect) => write!(f, "layout({indirect})"),
    }
}

fn format_evidence_captures(
    f: &mut fmt::Formatter<'_>,
    captures: &[StaticEvidence],
    env: &ModuleEnv<'_>,
) -> fmt::Result {
    if captures.is_empty() {
        return Ok(());
    }
    write!(f, "; captures: [")?;
    for (index, capture) in captures.iter().enumerate() {
        if index != 0 {
            write!(f, ", ")?;
        }
        format_static_evidence(f, capture, env)?;
    }
    write!(f, "]")
}

fn format_dictionary_definition(
    f: &mut fmt::Formatter<'_>,
    id: TraitDictionaryId,
    env: &ModuleEnv<'_>,
) -> fmt::Result {
    let Some(module) = env.module_by_id(id.module_id) else {
        return write!(f, "m{}:i{}", id.module_id, id.impl_id);
    };
    let Some(key) = module.get_impl_trait_key_by_id(id.impl_id) else {
        return write!(f, "m{}:i{}", id.module_id, id.impl_id);
    };
    let trait_def = env.trait_def(key.trait_id());
    let qualified_names = QualifiedNameEnv::new_from_module(module, env.modules);
    write!(
        f,
        "{}",
        qualified_names.qualified_impl_name(key.trait_id(), trait_def, key.input_tys())
    )
}

fn format_subscript_definition(
    f: &mut fmt::Formatter<'_>,
    id: SubscriptId,
    env: &ModuleEnv<'_>,
) -> fmt::Result {
    let Some(module) = env.module_by_id(id.module) else {
        return write!(f, "m{}:s{}", id.module, id.subscript);
    };
    let qualified_names = QualifiedNameEnv::new_from_module(module, env.modules);
    let readable_name = module
        .get_subscript_name_by_id(id.subscript)
        .map(|name| name.to_string())
        .or_else(|| {
            module
                .get_projection_key_by_subscript_id(id.subscript)
                .map(|key| qualified_names.qualified_projection_subscript_name(key))
        });
    match readable_name {
        Some(name) => write!(
            f,
            "{}",
            qualified_names.fully_qualified_subscript_name(id.module, &name)
        ),
        None => write!(f, "m{}:s{}", id.module, id.subscript),
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::*;
    use crate::std::math::float_type;

    #[test]
    fn constant_keys_preserve_signed_zero_in_nested_tuples() {
        let float = float_type();
        for nested in [false, true] {
            let constant = |value| {
                let mut ty = float;
                let mut representation = LiteralValue::new_native(Float::new(value).unwrap());
                if nested {
                    ty = Type::tuple([Type::tuple([float])]);
                    representation = LiteralValue::new_tuple(vec![LiteralValue::new_tuple(vec![
                        representation,
                    ])]);
                }
                Constant { ty, representation }
            };
            let positive = constant(0.0);
            let negative = constant(-0.0);
            assert_ne!(positive, negative);
            let mut keys = HashSet::new();
            keys.insert(positive);
            keys.insert(negative);
            assert!(keys.contains(&constant(0.0)));
            assert!(keys.contains(&constant(-0.0)));
            assert!(!keys.insert(constant(0.0)));
            assert!(!keys.insert(constant(-0.0)));
            assert_eq!(keys.len(), 2);
        }
    }
}
