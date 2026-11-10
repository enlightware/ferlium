// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Canonical keys and substitutions for alpha-equivalent trait applications.

use crate::{
    FxHashMap,
    hir::dictionary::DictionaryReq,
    module::{ConcreteTraitImplKey, TraitId},
    types::{
        effects::{EffType, Effect, EffectVar},
        mutability::{MutType, MutVar},
        r#type::{FnType, Type, TypeVar},
        type_inference::substitution::InstSubst,
        type_like::TypeLike,
        type_mapper::TypeMapper,
    },
};

#[derive(Default)]
/// Renames inference variables deterministically so alpha-equivalent trait queries share a cycle-detection key.
pub(super) struct AlphaCanonicalTypeMapper {
    ty_vars: FxHashMap<TypeVar, TypeVar>,
    mut_vars: FxHashMap<MutVar, MutVar>,
    effect_vars: FxHashMap<EffectVar, EffectVar>,
}

impl AlphaCanonicalTypeMapper {
    fn type_var(&mut self, var: TypeVar) -> TypeVar {
        let next = self.ty_vars.len() as u32;
        *self
            .ty_vars
            .entry(var)
            .or_insert_with(|| TypeVar::new(next))
    }

    fn mut_var(&mut self, var: MutVar) -> MutVar {
        let next = self.mut_vars.len() as u32;
        *self
            .mut_vars
            .entry(var)
            .or_insert_with(|| MutVar::new(next))
    }

    fn effect_var(&mut self, var: EffectVar) -> EffectVar {
        let next = self.effect_vars.len() as u32;
        *self
            .effect_vars
            .entry(var)
            .or_insert_with(|| EffectVar::new(next))
    }
}

impl TypeMapper for AlphaCanonicalTypeMapper {
    fn map_type(&mut self, ty: Type) -> Type {
        let Some(var) = ({ ty.data().as_variable().copied() }) else {
            return ty;
        };
        Type::variable(self.type_var(var))
    }

    fn map_mut_type(&mut self, mut_ty: MutType) -> MutType {
        match mut_ty {
            MutType::Variable(var) => MutType::variable(self.mut_var(var)),
            MutType::Resolved(_) => mut_ty,
        }
    }

    fn map_effect_type(&mut self, eff_ty: &EffType) -> EffType {
        EffType::from_vec(
            eff_ty
                .iter()
                .map(|effect| match effect {
                    Effect::Primitive(_) => effect,
                    Effect::Variable(var) => Effect::Variable(self.effect_var(var)),
                })
                .collect(),
        )
    }
}

/// Rename variables by deterministic first occurrence, preserving the structure and concrete parts
/// of the types. This is an identity only for compiler-generated artifacts whose variables remain
/// quantified; it must not replace semantic type identity in ordinary trait lookup.
pub(crate) fn alpha_canonicalize_types(types: &[Type]) -> Vec<Type> {
    let mut mapper = AlphaCanonicalTypeMapper::default();
    types.iter().map(|ty| ty.map(&mut mapper)).collect()
}

/// The identity of a generated dictionary: its trait application, inputs and outputs, renamed
/// together by first occurrence, as outputs may stay open in the caller's variables. Each output
/// effect is encoded as the effect of a nullary function type, so the key shares the representation
/// of input-keyed applications without colliding with them.
pub(crate) fn application_key(
    trait_id: TraitId,
    input_tys: &[Type],
    output_tys: Option<&[Type]>,
    output_effs: Option<&[EffType]>,
) -> ConcreteTraitImplKey {
    let mut mapper = AlphaCanonicalTypeMapper::default();
    let mut tys = input_tys
        .iter()
        .chain(output_tys.unwrap_or_default())
        .map(|ty| ty.map(&mut mapper))
        .collect::<Vec<_>>();
    if let Some(output_effs) = output_effs {
        tys.extend(output_effs.iter().map(|eff| {
            Type::function_type(FnType::new_by_val(
                [],
                Type::unit(),
                mapper.map_effect_type(eff),
            ))
        }));
    }
    ConcreteTraitImplKey::new(trait_id, tys)
}

/// Alpha-canonicalize types and return the instantiation from canonical variables back to the
/// caller's variables. Generated dictionary definitions use the canonical side; construction
/// sites apply the returned substitution to their capture schemas.
pub(crate) fn alpha_canonicalize_types_with_instantiation(
    types: &[Type],
) -> (Vec<Type>, InstSubst) {
    let mut mapper = AlphaCanonicalTypeMapper::default();
    let canonical = types.iter().map(|ty| ty.map(&mut mapper)).collect();
    let ty_subst = mapper
        .ty_vars
        .into_iter()
        .map(|(original, canonical)| (canonical, Type::variable(original)))
        .collect();
    let eff_subst = mapper
        .effect_vars
        .into_iter()
        .map(|(original, canonical)| (canonical, EffType::single_variable(original)))
        .collect();
    (canonical, (ty_subst, eff_subst))
}

pub(crate) fn alpha_canonicalize_dictionary_requirements(
    requirements: &[DictionaryReq],
) -> Vec<DictionaryReq> {
    let mut mapper = AlphaCanonicalTypeMapper::default();
    requirements
        .iter()
        .map(|requirement| requirement.instantiate(&mut mapper))
        .collect()
}
