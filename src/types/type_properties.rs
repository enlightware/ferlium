// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Structural properties of a concrete type, asked by more than one stage.
//!
//! Type inference and HIR elaboration ask through the trait solver; the MIR optimizer asks through a
//! `ModuleEnv`, having no solver. The query is the same, so it lives here as a free function over
//! the small environment it needs.
//!
//! `type_has_static_layout` in `std::value` is this module's sibling and belongs here too; it is
//! left where it is until something needs it moved.

use rustc_hash::FxHashSet;

use crate::{
    module::{ConcreteTraitImplKey, TraitId, TypeDefId},
    types::r#type::{Type, TypeDef, TypeKind},
    types::type_like::TypeLike,
};

/// What [`concrete_type_is_trivial_copy`] needs from whoever asks it.
pub(crate) trait TypePropertyEnv {
    /// Whether `ty` opts into `TrivialCopy` through an impl in the trait's own module.
    ///
    /// Probed in the module that owns the trait rather than in the current visibility scope, so a
    /// native-only marker property does not change when an unrelated module is added or removed.
    fn has_trivial_copy_impl(&self, ty: Type) -> bool;

    fn type_def(&self, id: TypeDefId) -> &TypeDef;
}

/// The key a `TrivialCopy` opt-in for `ty` is registered under, and the trait it belongs to.
pub(crate) fn trivial_copy_impl_key(trait_id: TraitId, ty: Type) -> ConcreteTraitImplKey {
    ConcreteTraitImplKey::new(trait_id, vec![ty])
}

/// Whether representation-copying this concrete type is semantically valid.
///
/// Native types opt in through concrete `TrivialCopy` impls. Inline product types derive the
/// property structurally, while named types do so only when they have no explicit custom `Value`
/// impl overriding ownership behaviour.
///
/// A non-recursive sum qualifies when every possible inline payload qualifies. A recursive
/// occurrence is indirect and owns its allocation, so the recursion check below rejects it.
pub(crate) fn concrete_type_is_trivial_copy(ty: Type, env: &impl TypePropertyEnv) -> bool {
    if !ty.is_constant() {
        return false;
    }
    is_trivial_copy(ty, &mut FxHashSet::default(), env)
}

fn is_trivial_copy(ty: Type, active: &mut FxHashSet<Type>, env: &impl TypePropertyEnv) -> bool {
    if env.has_trivial_copy_impl(ty) {
        return true;
    }
    // A recursive occurrence is represented indirectly, so it owns storage and cannot be copied by
    // representation.
    if !active.insert(ty) {
        return false;
    }

    let kind = ty.data().clone();
    let result = match kind {
        TypeKind::Tuple(member_tys) => member_tys
            .into_iter()
            .all(|member_ty| is_trivial_copy(member_ty, active, env)),
        TypeKind::Record(fields) => fields
            .into_iter()
            .all(|(_, field_ty)| is_trivial_copy(field_ty, active, env)),
        TypeKind::Named(named) => {
            let type_def = env.type_def(named.def);
            !type_def.has_custom_value_impl && {
                let shape_ty =
                    type_def.instantiated_shape_with_effects(&named.params, &named.effect_params);
                is_trivial_copy(shape_ty, active, env)
            }
        }
        // Non-recursive variant payloads are stored inline. The tag and union are representation-
        // copyable exactly when every possible payload is representation-copyable.
        TypeKind::Variant(cases) => cases
            .into_iter()
            .all(|(_, payload_ty)| is_trivial_copy(payload_ty, active, env)),
        TypeKind::Native(_)
        | TypeKind::Function(_)
        | TypeKind::Subscript(_)
        | TypeKind::Never
        | TypeKind::Variable(_) => false,
    };
    active.remove(&ty);
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CompilerSession, std::math::int_type, std::string::string_type};

    /// The two environments must agree, or a type would be copyable during elaboration and not
    /// during optimization — the property they share is the whole point of the abstraction.
    #[test]
    fn the_module_env_agrees_with_the_trait_solver() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let ordering = crate::std::ordering::ordering_type();
        for (ty, expected) in [
            (int_type(), true),
            (Type::unit(), true),
            (ordering, true),
            (string_type(), false),
            (Type::tuple([int_type(), int_type()]), true),
            (Type::tuple([int_type(), string_type()]), false),
            (Type::variant([(ustr::ustr("Some"), int_type())]), true),
            (Type::variant([(ustr::ustr("Some"), string_type())]), false),
        ] {
            assert_eq!(concrete_type_is_trivial_copy(ty, &env), expected, "{ty:?}");
        }
    }
}
