// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use crate::{
    hir::value::Value,
    module::TypeDefId,
    types::r#type::{NamedType, Type, TypeKind, variant_type},
};
use rustc_hash::FxHashSet;
use ustr::ustr;

pub fn option_type(inner: Type) -> Type {
    variant_type([("None", Type::unit()), ("Some", Type::tuple([inner]))])
}

pub fn option_type_generic() -> Type {
    option_type(Type::variable_id(0))
}

#[cfg(test)]
pub(crate) fn option_repr_payload_type_with(
    result: Type,
    named_repr: impl FnMut(&NamedType) -> Option<Type>,
) -> Option<Type> {
    try_option_repr_payload_type_with(result, named_repr)
        .ok()
        .flatten()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ReprResolutionError {
    Unavailable(TypeDefId),
    Cycle(Type),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum NativeOptionalContractError {
    ReprResolution(ReprResolutionError),
    MissingLowerEntry,
    UnexpectedLowerEntry,
    PayloadMismatch { ferlium: Type, rust: Type },
}

/// Validate and return the payload when the resolved representation is exactly
/// `None(()) | Some((T,))` and it matches the native lower entry.
///
/// Recognition is representation-based rather than tied to the current `Option<T>` alias, so a
/// future named Option newtype can retain the native optional-result contract by keeping this
/// representation. Both registration and physical lowering use this function so they cannot
/// disagree about how far through named representations to resolve.
pub(crate) fn native_optional_payload_contract_with(
    result: Type,
    native_payload: Option<Type>,
    mut named_repr: impl FnMut(&NamedType) -> Option<Type>,
) -> Result<Option<Type>, NativeOptionalContractError> {
    let repr_payload = try_option_repr_payload_type_with(result, &mut named_repr)
        .map_err(NativeOptionalContractError::ReprResolution)?;
    let (repr_payload, native_payload) = match (repr_payload, native_payload) {
        (None, None) => return Ok(None),
        (Some(_), None) => return Err(NativeOptionalContractError::MissingLowerEntry),
        (None, Some(_)) => return Err(NativeOptionalContractError::UnexpectedLowerEntry),
        (Some(repr_payload), Some(native_payload)) => (repr_payload, native_payload),
    };
    let repr_payload = try_resolve_repr_type_with(repr_payload, &mut named_repr)
        .map_err(NativeOptionalContractError::ReprResolution)?;
    let native_payload = try_resolve_repr_type_with(native_payload, named_repr)
        .map_err(NativeOptionalContractError::ReprResolution)?;
    if repr_payload != native_payload {
        return Err(NativeOptionalContractError::PayloadMismatch {
            ferlium: repr_payload,
            rust: native_payload,
        });
    }
    Ok(Some(repr_payload))
}

fn try_option_repr_payload_type_with(
    result: Type,
    named_repr: impl FnMut(&NamedType) -> Option<Type>,
) -> Result<Option<Type>, ReprResolutionError> {
    let result = try_resolve_repr_type_with(result, named_repr)?;
    let cases = match &*result.data() {
        TypeKind::Variant(cases) => cases.clone(),
        _ => return Ok(None),
    };
    if cases.len() != 2 {
        return Ok(None);
    }
    let Some(none) = cases.iter().find(|(name, _)| *name == ustr("None")) else {
        return Ok(None);
    };
    let none = none.1;
    if none != Type::unit() {
        return Ok(None);
    }
    let Some(some) = cases.iter().find(|(name, _)| *name == ustr("Some")) else {
        return Ok(None);
    };
    let some = some.1;
    let payload = match &*some.data() {
        TypeKind::Tuple(payload) => payload.clone(),
        _ => return Ok(None),
    };
    let [payload] = payload.as_slice() else {
        return Ok(None);
    };
    Ok(Some(*payload))
}

fn try_resolve_repr_type_with(
    mut result: Type,
    mut named_repr: impl FnMut(&NamedType) -> Option<Type>,
) -> Result<Type, ReprResolutionError> {
    let mut active = FxHashSet::default();
    loop {
        let named = match &*result.data() {
            TypeKind::Named(named) => named.clone(),
            _ => return Ok(result),
        };
        if !active.insert(result) {
            return Err(ReprResolutionError::Cycle(result));
        }
        result = named_repr(&named).ok_or(ReprResolutionError::Unavailable(named.def))?;
    }
}

pub fn none() -> Value {
    Value::unit_variant(ustr("None"))
}

pub fn some(value: Value) -> Value {
    Value::tuple_variant(ustr("Some"), [value])
}

#[cfg(test)]
mod tests {
    use crate::{
        module::{LocalTypeDefId, ModuleId, TypeDefId, id::Id},
        std::{logic::bool_type, math::int_type},
        types::r#type::variant_type,
    };

    use super::*;

    #[test]
    fn optional_native_result_is_recognized_through_a_named_repr() {
        let definition = TypeDefId::new(ModuleId::new(7), LocalTypeDefId::from_index(0));
        let named = Type::named(definition, [int_type()]);
        let payload = option_repr_payload_type_with(named, |named| {
            assert_eq!(named.def, definition);
            Some(option_type(named.params[0]))
        });

        assert_eq!(payload, Some(int_type()));
    }

    #[test]
    fn optional_native_result_requires_the_exact_repr_shape() {
        let direct_payload = variant_type([("None", Type::unit()), ("Some", int_type())]);
        let renamed_case = variant_type([
            ("Absent", Type::unit()),
            ("Some", Type::tuple([int_type()])),
        ]);
        let extra_case = variant_type([
            ("None", Type::unit()),
            ("Some", Type::tuple([int_type()])),
            ("Other", Type::tuple([bool_type()])),
        ]);

        assert_eq!(
            option_repr_payload_type_with(option_type(int_type()), |_| None),
            Some(int_type())
        );
        assert_eq!(
            option_repr_payload_type_with(direct_payload, |_| None),
            None
        );
        assert_eq!(option_repr_payload_type_with(renamed_case, |_| None), None);
        assert_eq!(option_repr_payload_type_with(extra_case, |_| None), None);
    }
}
