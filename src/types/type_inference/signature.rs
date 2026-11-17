// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use super::unify::UnifiedTypeInference;
use crate::{
    FxHashSet,
    compiler::error::InvalidDefaultMethodKind,
    types::{
        effects::EffType,
        r#type::{FnType, Type},
        type_scheme::TypeScheme,
    },
};

/// Check the generality of an instantiated declared signature after body inference.
/// The declaration's variables must still be independent variables: unification may
/// rename them, but must not specialize or identify them. The obligations left by the
/// body are reduced to the declaration's afterwards, as under a complete clause.
pub(crate) fn check_declared_signature(
    declaration: &TypeScheme<FnType>,
    inference: &mut UnifiedTypeInference,
) -> Result<(), InvalidDefaultMethodKind> {
    let mut types = FxHashSet::default();
    for var in &declaration.ty_quantifiers {
        let ty = inference.substitute_in_type(Type::variable(*var));
        if !ty.data().is_variable() || !types.insert(ty) {
            return Err(InvalidDefaultMethodKind::SpecializedTypeParameter);
        }
    }
    let mut effects = FxHashSet::default();
    for var in &declaration.eff_quantifiers {
        let effect = inference.substitute_in_effect_type(&EffType::single_variable(*var));
        if effect.to_single_variable().is_none() || !effects.insert(effect) {
            return Err(InvalidDefaultMethodKind::RestrictedEffectParameter);
        }
    }
    Ok(())
}
