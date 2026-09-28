// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use super::unify::UnifiedTypeInference;
use crate::{
    FxHashSet,
    compiler::error::InvalidDefaultMethodKind,
    types::{
        effects::EffType,
        r#type::{FnType, Type},
        type_scheme::{PubTypeConstraint, TypeScheme},
    },
};

/// Check the generality of an instantiated declared signature after body inference.
/// The declaration's variables must still be independent variables: unification may
/// rename them, but must not specialize or identify them. Obligations left by the
/// body must be provided by the declaration. Concrete obligations have already been
/// discharged by inference.
pub(crate) fn check_declared_signature<'a>(
    declaration: &TypeScheme<FnType>,
    inferred_constraints: impl IntoIterator<Item = &'a PubTypeConstraint>,
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
    let givens = declaration
        .constraints
        .iter()
        .map(|constraint| inference.substitute_in_constraint(constraint))
        .collect::<Vec<_>>();
    if inferred_constraints
        .into_iter()
        .any(|constraint| !givens.contains(constraint))
    {
        return Err(InvalidDefaultMethodKind::UndeclaredConstraint);
    }
    Ok(())
}
