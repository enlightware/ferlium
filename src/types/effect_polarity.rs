// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! The polarity of effect variables: whether a type performs or receives their effects.

use crate::{
    FxHashSet,
    module::TraitId,
    types::{
        effects::{EffType, EffectVar},
        mutability::MutType,
        r#trait::Trait,
        r#type::{FnType, Type, TypeKind},
        type_like::TypeLike,
        type_scheme::PubTypeConstraint,
    },
};

/// How an effect variable occurs: in effects that are performed, in effects that are received,
/// or both, which includes the effect arguments of named types.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum EffectPolarity {
    /// Only in performed effects, so a smaller row may stand for a larger one.
    Positive,
    /// Only in received effects, such as a callback's, so a larger row may stand for a smaller one.
    Negative,
    /// In both, so the rows must be equal.
    Invariant,
}

/// The positions in which effect variables occur, positive ones being performed and negative
/// ones received; invariant occurrences count as both.
#[derive(Default)]
pub(crate) struct EffectVarPolarities {
    positive: FxHashSet<EffectVar>,
    negative: FxHashSet<EffectVar>,
    visited: FxHashSet<(Type, bool)>,
}

impl EffectVarPolarities {
    pub(crate) fn positive_only(self) -> FxHashSet<EffectVar> {
        self.positive
            .into_iter()
            .filter(|var| !self.negative.contains(var))
            .collect()
    }

    /// The polarity of `var`, if it occurs.
    pub(crate) fn polarity(&self, var: EffectVar) -> Option<EffectPolarity> {
        match (self.positive.contains(&var), self.negative.contains(&var)) {
            (true, false) => Some(EffectPolarity::Positive),
            (false, true) => Some(EffectPolarity::Negative),
            (true, true) => Some(EffectPolarity::Invariant),
            (false, false) => None,
        }
    }

    pub(crate) fn visit_effects_with_polarity(
        &mut self,
        effects: &EffType,
        polarity: EffectPolarity,
    ) {
        match polarity {
            EffectPolarity::Positive => self.visit_effects(effects, true),
            EffectPolarity::Negative => self.visit_effects(effects, false),
            EffectPolarity::Invariant => {
                self.visit_effects(effects, true);
                self.visit_effects(effects, false);
            }
        }
    }

    fn visit_effects(&mut self, effects: &EffType, positive: bool) {
        let vars = if positive {
            &mut self.positive
        } else {
            &mut self.negative
        };
        effects.fill_with_inner_effect_vars(vars);
    }

    pub(crate) fn visit_fn(&mut self, fn_ty: &FnType, positive: bool) {
        for arg in &fn_ty.args {
            self.visit(arg.ty, !positive);
            if arg.mut_ty != MutType::constant() {
                self.visit(arg.ty, positive);
            }
        }
        self.visit(fn_ty.ret, positive);
        self.visit_effects(&fn_ty.effects, positive);
    }

    pub(crate) fn visit(&mut self, ty: Type, positive: bool) {
        if !self.visited.insert((ty, positive)) {
            return;
        }
        use TypeKind::*;
        match &*ty.data() {
            Variable(_) | Never => {}
            Native(native) => {
                for arg in &native.arguments {
                    self.visit(*arg, positive);
                }
            }
            Variant(types) | Record(types) => {
                for (_, ty) in types {
                    self.visit(*ty, positive);
                }
            }
            Tuple(types) => {
                for ty in types {
                    self.visit(*ty, positive);
                }
            }
            Function(fn_ty) => self.visit_fn(fn_ty, positive),
            Subscript(subscript) => {
                for arg in &subscript.args {
                    self.visit(arg.ty, !positive);
                    self.visit(arg.ty, positive);
                }
                self.visit(subscript.ret, positive);
                self.visit(subscript.ret, !positive);
                for member in subscript.members() {
                    self.visit_effects(&member.effects, positive);
                }
            }
            Named(named) => {
                for param in &named.params {
                    self.visit(*param, positive);
                    self.visit(*param, !positive);
                }
                for effects in &named.effect_params {
                    self.visit_effects(effects, positive);
                    self.visit_effects(effects, !positive);
                }
            }
        }
    }
}

/// The polarity of each output effect of the trait `trait_id`, from its occurrences in the
/// trait's method signatures and, through the trait's constraints, in other traits' outputs. An
/// output effect that occurs nowhere is positive.
pub(crate) fn trait_output_effect_polarities<'a>(
    trait_id: TraitId,
    trait_def: &dyn Fn(TraitId) -> &'a Trait,
) -> Vec<EffectPolarity> {
    output_effect_polarities_inner(trait_id, trait_def, &mut Vec::new())
}

fn output_effect_polarities_inner<'a>(
    trait_id: TraitId,
    trait_def: &dyn Fn(TraitId) -> &'a Trait,
    visiting: &mut Vec<TraitId>,
) -> Vec<EffectPolarity> {
    let def = trait_def(trait_id);
    let count = def.output_effect_count() as usize;
    if visiting.contains(&trait_id) {
        return vec![EffectPolarity::Invariant; count];
    }
    visiting.push(trait_id);
    let mut polarities = EffectVarPolarities::default();
    for (_, method) in &def.methods {
        polarities.visit_fn(&method.ty_scheme.ty, true);
    }
    for constraint in def.constraints.iter().chain(&def.parent_constraints) {
        match constraint {
            PubTypeConstraint::HaveTrait {
                trait_id: other_trait_id,
                input_tys,
                output_tys,
                output_effs,
                ..
            } => {
                for ty in input_tys.iter().chain(output_tys) {
                    polarities.visit(*ty, true);
                    polarities.visit(*ty, false);
                }
                let other = output_effect_polarities_inner(*other_trait_id, trait_def, visiting);
                for (effects, polarity) in output_effs.iter().zip(other) {
                    polarities.visit_effects_with_polarity(effects, polarity);
                }
            }
            constraint => {
                let mut vars = FxHashSet::default();
                constraint.fill_with_inner_effect_vars(&mut vars);
                let effects = EffType::multiple_variable(&vars.into_iter().collect::<Vec<_>>());
                polarities.visit_effects_with_polarity(&effects, EffectPolarity::Invariant);
            }
        }
    }
    visiting.pop();
    (0..count)
        .map(|index| {
            polarities
                .polarity(EffectVar::new(index as u32))
                .unwrap_or(EffectPolarity::Positive)
        })
        .collect()
}
