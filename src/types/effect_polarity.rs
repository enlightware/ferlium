// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! The polarity of effect variables: whether a type performs or receives their effects.

use crate::{
    FxHashMap, FxHashSet,
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
    let mut walk = PolarityWalk {
        trait_def,
        visiting: Vec::new(),
        settled: FxHashMap::default(),
    };
    walk.polarities(trait_id).0
}

/// One query of [`trait_output_effect_polarities`]. A trait met again while its polarities are
/// being computed is taken as invariant, so the polarities of a trait on a cycle depend on where
/// the cycle is entered; those of the others do not, and are computed once, as traits whose
/// constraints share other traits would otherwise be walked once per path.
struct PolarityWalk<'a, 'd> {
    trait_def: &'d dyn Fn(TraitId) -> &'a Trait,
    /// The traits being walked, outermost first.
    visiting: Vec<TraitId>,
    settled: FxHashMap<TraitId, Vec<EffectPolarity>>,
}

impl PolarityWalk<'_, '_> {
    /// The polarities of `trait_id`, and the outermost position in [`Self::visiting`] that they
    /// depend on, if any.
    fn polarities(&mut self, trait_id: TraitId) -> (Vec<EffectPolarity>, Option<usize>) {
        let def = (self.trait_def)(trait_id);
        let count = def.output_effect_count() as usize;
        if count == 0 {
            return (Vec::new(), None);
        }
        if let Some(polarities) = self.settled.get(&trait_id) {
            return (polarities.clone(), None);
        }
        if let Some(position) = self.visiting.iter().position(|&id| id == trait_id) {
            return (vec![EffectPolarity::Invariant; count], Some(position));
        }
        let depth = self.visiting.len();
        self.visiting.push(trait_id);
        let mut depends_on: Option<usize> = None;
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
                    let (other, other_depends_on) = self.polarities(*other_trait_id);
                    depends_on = match (depends_on, other_depends_on) {
                        (Some(a), Some(b)) => Some(a.min(b)),
                        (a, b) => a.or(b),
                    };
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
        self.visiting.pop();
        let result: Vec<_> = (0..count)
            .map(|index| {
                polarities
                    .polarity(EffectVar::new(index as u32))
                    .unwrap_or(EffectPolarity::Positive)
            })
            .collect();
        // A trait whose walk met neither itself nor a trait above it reaches no trait of any walk
        // that meets it, which would then be on a cycle with it: its polarities are the same there.
        if depends_on.is_none() {
            self.settled.insert(trait_id, result.clone());
        }
        (result, depends_on.filter(|&position| position < depth))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        Location,
        module::{LocalTraitId, ModuleId},
        parser::location::InstantiableLocation,
        types::type_scheme::ConstraintOrigin,
        ustr,
    };

    fn trait_id(index: u32) -> TraitId {
        TraitId::new(ModuleId::new(0), LocalTraitId::new(index))
    }

    /// A trait with one output effect, requiring `Self` to implement each of `requirements` with
    /// the given output effect.
    fn trait_requiring(name: &str, requirements: &[(u32, EffType)]) -> Trait {
        let mut trait_def = Trait::new(name, "", ["Self"], [], []);
        trait_def.output_effect_names = vec![ustr("E")];
        trait_def.constraints = requirements
            .iter()
            .map(|(index, effects)| PubTypeConstraint::HaveTrait {
                origin: ConstraintOrigin::default(),
                trait_id: trait_id(*index),
                input_tys: vec![Type::variable_id(0)],
                output_tys: vec![],
                output_effs: vec![effects.clone()],
                span: InstantiableLocation::new(Location::new_synthesized()),
            })
            .collect();
        trait_def
    }

    #[test]
    fn polarities_of_a_cycle_depend_on_where_it_is_entered() {
        // `A` passes its effect to `B`, which requires `A` without effects. `Root` requires `B`
        // without effects, then `A` with its own effect. Through `B`, `A` is met while `B` is
        // being walked, so its effect is invariant there; met directly, it is positive, which is
        // what `Root` passes its effect to: the walk through `B` must not settle `A`.
        let own = EffType::single_variable_id(0);
        let (a, b, root) = (0, 1, 2);
        let traits = [
            trait_requiring("A", &[(b, own.clone())]),
            trait_requiring("B", &[(a, EffType::empty())]),
            trait_requiring("Root", &[(b, EffType::empty()), (a, own)]),
        ];
        let trait_def = |id: TraitId| &traits[id.index.as_u32() as usize];
        let polarities = |index| trait_output_effect_polarities(trait_id(index), &trait_def);
        assert_eq!(polarities(root), [EffectPolarity::Positive]);
        assert_eq!(polarities(a), [EffectPolarity::Positive]);
        assert_eq!(polarities(b), [EffectPolarity::Positive]);
    }
}
