// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{
    cmp::Ordering,
    fmt::{self, Display},
    iter::FusedIterator,
};

use crate::{FxHashMap, FxHashSet};

use derive_new::new;
use enum_as_inner::EnumAsInner;

use crate::format::{type_variable_subscript, write_with_separator};

/// An effect describing the non-pure behavior of a function
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PrimitiveEffect {
    Read,
    Write,
    Fallible,
}

impl Display for PrimitiveEffect {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use PrimitiveEffect::*;
        match self {
            Read => write!(f, "read"),
            Write => write!(f, "write"),
            Fallible => write!(f, "fallible"),
        }
    }
}

/// A generic variable for effects
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, new)]
pub struct EffectVar {
    /// The name of this effect variable, its identity in the context considered
    name: u32,
}

impl EffectVar {
    pub fn name(&self) -> u32 {
        self.name
    }
}

impl Display for EffectVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "e{}", type_variable_subscript(self.name))
    }
}

pub type EffectVarKey = EffectVar;

/// An effect, can be a primitive effect or a variable effect
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, EnumAsInner)]
pub enum Effect {
    Primitive(PrimitiveEffect),
    Variable(EffectVar),
}

impl Display for Effect {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Effect::Primitive(effect) => write!(f, "{effect}"),
            Effect::Variable(var) => write!(f, "{var}"),
        }
    }
}

const PRIMITIVE_EFFECTS: [PrimitiveEffect; 3] = [
    PrimitiveEffect::Read,
    PrimitiveEffect::Write,
    PrimitiveEffect::Fallible,
];

type InlineVarBits = usize;
type PrimitiveEffectsStorage = u16;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
struct PrimitiveEffects(PrimitiveEffectsStorage);

impl PrimitiveEffects {
    const READ: PrimitiveEffectsStorage = 1 << 0;
    const WRITE: PrimitiveEffectsStorage = 1 << 1;
    const FALLIBLE: PrimitiveEffectsStorage = 1 << 2;

    fn insert(&mut self, effect: PrimitiveEffect) {
        self.0 |= Self::bit(effect);
    }

    fn union_with(&mut self, other: Self) {
        self.0 |= other.0;
    }

    fn contains(self, effect: PrimitiveEffect) -> bool {
        (self.0 & Self::bit(effect)) != 0
    }

    fn is_empty(self) -> bool {
        self.0 == 0
    }

    fn len(self) -> usize {
        self.0.count_ones() as usize
    }

    fn iter(self) -> PrimitiveEffectsIter {
        PrimitiveEffectsIter {
            bits: self,
            index: 0,
        }
    }

    fn bit(effect: PrimitiveEffect) -> PrimitiveEffectsStorage {
        match effect {
            PrimitiveEffect::Read => Self::READ,
            PrimitiveEffect::Write => Self::WRITE,
            PrimitiveEffect::Fallible => Self::FALLIBLE,
        }
    }
}

struct PrimitiveEffectsIter {
    bits: PrimitiveEffects,
    index: usize,
}

impl Iterator for PrimitiveEffectsIter {
    type Item = PrimitiveEffect;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(effect) = PRIMITIVE_EFFECTS.get(self.index).copied() {
            self.index += 1;
            if self.bits.contains(effect) {
                return Some(effect);
            }
        }
        None
    }
}

impl FusedIterator for PrimitiveEffectsIter {}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Effects {
    Inline {
        primitive_bits: PrimitiveEffects,
        var_bits: InlineVarBits,
    },
    Heap(Box<HeapEffects>),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct HeapEffects {
    primitive_bits: PrimitiveEffects,
    variables: Vec<EffectVar>,
}

impl Default for Effects {
    fn default() -> Self {
        Self::Inline {
            primitive_bits: PrimitiveEffects::default(),
            var_bits: 0,
        }
    }
}

/// An effects type, consisting of a set of effects.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct EffType(Effects);
impl EffType {
    pub fn empty() -> Self {
        Self::default()
    }
    pub fn single(effect: Effect) -> Self {
        let mut effects = Self::empty();
        effects.insert(effect);
        effects
    }
    pub fn single_primitive(effect: PrimitiveEffect) -> Self {
        let mut primitives = PrimitiveEffects::default();
        primitives.insert(effect);
        Self(Effects::Inline {
            primitive_bits: primitives,
            var_bits: 0,
        })
    }
    pub fn single_variable(var: EffectVar) -> Self {
        if let Some(var_bit) = inline_var_bit(var) {
            Self(Effects::Inline {
                primitive_bits: PrimitiveEffects::default(),
                var_bits: var_bit,
            })
        } else {
            Self(Effects::Heap(Box::new(HeapEffects {
                primitive_bits: PrimitiveEffects::default(),
                variables: vec![var],
            })))
        }
    }
    pub fn single_variable_id(id: u32) -> Self {
        Self::single_variable(EffectVar::new(id))
    }
    pub fn multiple(effects: &[Effect]) -> Self {
        effects.iter().copied().collect()
    }
    pub fn multiple_primitive(effects: &[PrimitiveEffect]) -> Self {
        let mut primitives = PrimitiveEffects::default();
        for effect in effects {
            primitives.insert(*effect);
        }
        Self(Effects::Inline {
            primitive_bits: primitives,
            var_bits: 0,
        })
    }
    pub fn multiple_variable(vars: &[EffectVar]) -> Self {
        vars.iter().copied().map(Effect::Variable).collect()
    }

    pub fn from_vec(effects: Vec<Effect>) -> Self {
        effects.into_iter().collect()
    }

    pub fn insert(&mut self, effect: Effect) {
        match effect {
            Effect::Primitive(effect) => self.insert_primitive(effect),
            Effect::Variable(var) => self.insert_variable(var),
        }
    }

    pub fn extend(&mut self, other: &Self) {
        match (&mut self.0, &other.0) {
            (
                Effects::Inline {
                    primitive_bits: left_primitives,
                    var_bits: left_vars,
                },
                Effects::Inline {
                    primitive_bits: right_primitives,
                    var_bits: right_vars,
                },
            ) => {
                left_primitives.union_with(*right_primitives);
                *left_vars |= *right_vars;
            }
            (Effects::Inline { .. }, Effects::Heap(right)) => {
                let mut heap = self.to_heap_effects();
                heap.primitive_bits.union_with(right.primitive_bits);
                extend_variables(&mut heap.variables, &right.variables);
                self.0 = Effects::Heap(Box::new(heap));
            }
            (
                Effects::Heap(left),
                Effects::Inline {
                    primitive_bits,
                    var_bits,
                },
            ) => {
                left.primitive_bits.union_with(*primitive_bits);
                extend_variables_from_bits(&mut left.variables, *var_bits);
            }
            (Effects::Heap(left), Effects::Heap(right)) => {
                left.primitive_bits.union_with(right.primitive_bits);
                extend_variables(&mut left.variables, &right.variables);
            }
        }
    }

    pub fn union(&self, other: &Self) -> Self {
        let mut new = self.clone();
        new.extend(other);
        new
    }

    pub fn to_single_variable(&self) -> Option<EffectVar> {
        if !self.primitives().is_empty() {
            None
        } else if self.variables_len() == 1 {
            self.variables().next()
        } else {
            None
        }
    }

    pub fn is_only_vars(&self) -> bool {
        self.primitives().is_empty()
    }

    pub fn has_variables(&self) -> bool {
        self.variables_len() != 0
    }

    fn has_variable_in_substitution(&self, subst: &EffectsInstSubst) -> bool {
        self.variables().any(|var| subst.contains_key(&var))
    }

    pub fn to_multiple_vars(&self) -> Option<Vec<EffectVar>> {
        if self.is_only_vars() {
            Some(self.variables().collect())
        } else {
            None
        }
    }

    pub fn inner_vars(&self) -> Vec<EffectVar> {
        self.variables().collect()
    }

    pub fn inner_non_vars(&self) -> Vec<PrimitiveEffect> {
        self.primitives().iter().collect()
    }

    pub fn any(&self) -> bool {
        !self.is_empty()
    }

    pub fn is_empty(&self) -> bool {
        self.primitives().is_empty() && self.variables_len() == 0
    }

    pub fn contains(&self, effect: Effect) -> bool {
        match effect {
            Effect::Primitive(effect) => self.primitives().contains(effect),
            Effect::Variable(var) => self.contains_variable(var),
        }
    }

    /// Returns true if all effects in self are also in other.
    /// This is a conservative check: if self contains any effect variables, it returns false.
    pub fn is_subset_of(&self, other: &Self) -> bool {
        // If self has any effect variables, we cannot guarantee it is a subset
        if self.has_variables() {
            return false;
        }
        self.inner_non_vars()
            .iter()
            .all(|e| other.contains(Effect::Primitive(*e)))
    }

    pub fn iter(&self) -> EffTypeIter<'_> {
        EffTypeIter {
            primitives: self.primitives().iter(),
            variables: self.variables(),
        }
    }

    pub fn as_single(&self) -> Option<Effect> {
        match (self.primitives().len(), self.variables_len()) {
            (1, 0) => self.primitives().iter().next().map(Effect::Primitive),
            (0, 1) => self.variables().next().map(Effect::Variable),
            _ => None,
        }
    }

    pub fn fill_with_inner_effect_vars(&self, vars: &mut FxHashSet<EffectVar>) {
        for var in self.variables() {
            vars.insert(var);
        }
    }

    pub fn instantiate(&self, subst: &EffectsInstSubst) -> Self {
        if self.is_empty() || subst.is_empty() || !self.has_variable_in_substitution(subst) {
            return self.clone();
        }

        if let Some(Effect::Variable(var)) = self.as_single() {
            return subst.get(&var).cloned().unwrap_or_else(|| self.clone());
        }

        let mut effects = Self(Effects::Inline {
            primitive_bits: self.primitives(),
            var_bits: 0,
        });
        for var in self.variables() {
            match subst.get(&var) {
                Some(subst) => effects.extend(subst),
                None => effects.insert(Effect::Variable(var)),
            }
        }
        effects
    }

    fn primitives(&self) -> PrimitiveEffects {
        match &self.0 {
            Effects::Inline { primitive_bits, .. } => *primitive_bits,
            Effects::Heap(heap) => heap.primitive_bits,
        }
    }

    fn variables_len(&self) -> usize {
        match &self.0 {
            Effects::Inline { var_bits, .. } => var_bits.count_ones() as usize,
            Effects::Heap(heap) => heap.variables.len(),
        }
    }

    fn variables(&self) -> EffectVarsIter<'_> {
        match &self.0 {
            Effects::Inline { var_bits, .. } => EffectVarsIter::Inline(InlineEffectVars {
                remaining_bits: *var_bits,
            }),
            Effects::Heap(heap) => EffectVarsIter::Heap(heap.variables.iter().copied()),
        }
    }

    fn insert_primitive(&mut self, effect: PrimitiveEffect) {
        match &mut self.0 {
            Effects::Inline { primitive_bits, .. } => primitive_bits.insert(effect),
            Effects::Heap(heap) => heap.primitive_bits.insert(effect),
        }
    }

    fn insert_variable(&mut self, var: EffectVar) {
        match &mut self.0 {
            Effects::Inline { var_bits, .. } => {
                if let Some(var_bit) = inline_var_bit(var) {
                    *var_bits |= var_bit;
                } else {
                    let mut heap = self.to_heap_effects();
                    insert_variable(&mut heap.variables, var);
                    self.0 = Effects::Heap(Box::new(heap));
                }
            }
            Effects::Heap(heap) => insert_variable(&mut heap.variables, var),
        }
    }

    fn contains_variable(&self, var: EffectVar) -> bool {
        match &self.0 {
            Effects::Inline { var_bits, .. } => {
                inline_var_bit(var).is_some_and(|bit| (*var_bits & bit) != 0)
            }
            Effects::Heap(heap) => heap.variables.binary_search(&var).is_ok(),
        }
    }

    fn to_heap_effects(&self) -> HeapEffects {
        HeapEffects {
            primitive_bits: self.primitives(),
            variables: self.variables().collect(),
        }
    }
}

impl Ord for EffType {
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

impl PartialOrd for EffType {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

pub struct EffTypeIter<'a> {
    primitives: PrimitiveEffectsIter,
    variables: EffectVarsIter<'a>,
}

pub struct EffTypeIntoIter {
    primitives: PrimitiveEffectsIter,
    variables: EffectVarsIntoIter,
}

enum EffectVarsIter<'a> {
    Inline(InlineEffectVars),
    Heap(std::iter::Copied<std::slice::Iter<'a, EffectVar>>),
}

enum EffectVarsIntoIter {
    Inline(InlineEffectVars),
    Heap(std::vec::IntoIter<EffectVar>),
}

impl Iterator for EffectVarsIter<'_> {
    type Item = EffectVar;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            EffectVarsIter::Inline(vars) => vars.next(),
            EffectVarsIter::Heap(vars) => vars.next(),
        }
    }
}

impl FusedIterator for EffectVarsIter<'_> {}

impl Iterator for EffectVarsIntoIter {
    type Item = EffectVar;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            EffectVarsIntoIter::Inline(vars) => vars.next(),
            EffectVarsIntoIter::Heap(vars) => vars.next(),
        }
    }
}

impl FusedIterator for EffectVarsIntoIter {}

struct InlineEffectVars {
    remaining_bits: InlineVarBits,
}

impl Iterator for InlineEffectVars {
    type Item = EffectVar;

    fn next(&mut self) -> Option<Self::Item> {
        let next = self.remaining_bits.trailing_zeros();
        if next == InlineVarBits::BITS {
            None
        } else {
            self.remaining_bits &= !(1 as InlineVarBits) << next;
            Some(EffectVar::new(next))
        }
    }
}

impl FusedIterator for InlineEffectVars {}

impl Iterator for EffTypeIter<'_> {
    type Item = Effect;

    fn next(&mut self) -> Option<Self::Item> {
        self.primitives
            .next()
            .map(Effect::Primitive)
            .or_else(|| self.variables.next().map(Effect::Variable))
    }
}

impl FusedIterator for EffTypeIter<'_> {}

impl Iterator for EffTypeIntoIter {
    type Item = Effect;

    fn next(&mut self) -> Option<Self::Item> {
        self.primitives
            .next()
            .map(Effect::Primitive)
            .or_else(|| self.variables.next().map(Effect::Variable))
    }
}

impl FusedIterator for EffTypeIntoIter {}

fn inline_var_bit(var: EffectVar) -> Option<InlineVarBits> {
    if var.name() < InlineVarBits::BITS {
        Some((1 as InlineVarBits) << var.name())
    } else {
        None
    }
}

fn insert_variable(variables: &mut Vec<EffectVar>, var: EffectVar) {
    if let Err(index) = variables.binary_search(&var) {
        variables.insert(index, var);
    }
}

fn extend_variables_from_bits(variables: &mut Vec<EffectVar>, var_bits: InlineVarBits) {
    for var in (InlineEffectVars {
        remaining_bits: var_bits,
    }) {
        insert_variable(variables, var);
    }
}

fn extend_variables(variables: &mut Vec<EffectVar>, other: &[EffectVar]) {
    if other.is_empty() {
        return;
    }
    if variables.is_empty() {
        variables.extend_from_slice(other);
        return;
    }
    if other.len() == 1 {
        insert_variable(variables, other[0]);
        return;
    }

    let mut merged = Vec::with_capacity(variables.len() + other.len());
    let mut left = variables.iter().copied().peekable();
    let mut right = other.iter().copied().peekable();

    loop {
        match (left.peek().copied(), right.peek().copied()) {
            (Some(a), Some(b)) if a < b => {
                merged.push(a);
                left.next();
            }
            (Some(a), Some(b)) if a > b => {
                merged.push(b);
                right.next();
            }
            (Some(a), Some(_)) => {
                merged.push(a);
                left.next();
                right.next();
            }
            (Some(a), None) => {
                merged.push(a);
                left.next();
            }
            (None, Some(b)) => {
                merged.push(b);
                right.next();
            }
            (None, None) => break,
        }
    }
    *variables = merged;
}

impl IntoIterator for EffType {
    type Item = Effect;
    type IntoIter = EffTypeIntoIter;

    fn into_iter(self) -> Self::IntoIter {
        match self.0 {
            Effects::Inline {
                primitive_bits,
                var_bits,
            } => EffTypeIntoIter {
                primitives: primitive_bits.iter(),
                variables: EffectVarsIntoIter::Inline(InlineEffectVars {
                    remaining_bits: var_bits,
                }),
            },
            Effects::Heap(heap) => EffTypeIntoIter {
                primitives: heap.primitive_bits.iter(),
                variables: EffectVarsIntoIter::Heap(heap.variables.into_iter()),
            },
        }
    }
}

impl FromIterator<Effect> for EffType {
    fn from_iter<T: IntoIterator<Item = Effect>>(iter: T) -> Self {
        let mut primitives = PrimitiveEffects::default();
        let mut inline_vars = 0 as InlineVarBits;
        let mut heap_variables = Vec::new();
        for effect in iter {
            match effect {
                Effect::Primitive(effect) => primitives.insert(effect),
                Effect::Variable(var) => match inline_var_bit(var) {
                    Some(bit) if heap_variables.is_empty() => inline_vars |= bit,
                    Some(_) => heap_variables.push(var),
                    None => {
                        if heap_variables.is_empty() {
                            heap_variables.extend(InlineEffectVars {
                                remaining_bits: inline_vars,
                            });
                        }
                        heap_variables.push(var);
                    }
                },
            }
        }

        if heap_variables.is_empty() {
            Self(Effects::Inline {
                primitive_bits: primitives,
                var_bits: inline_vars,
            })
        } else {
            heap_variables.sort();
            heap_variables.dedup();
            Self(Effects::Heap(Box::new(HeapEffects {
                primitive_bits: primitives,
                variables: heap_variables,
            })))
        }
    }
}

impl Display for EffType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write_with_separator(self.iter(), ", ", f)
    }
}

pub(crate) fn format_effect_binding_value(
    eff: &EffType,
    f: &mut fmt::Formatter<'_>,
) -> fmt::Result {
    match eff.as_single() {
        Some(effect) => effect.fmt(f),
        None if eff.is_empty() => write!(f, "()"),
        None => write!(f, "({eff})"),
    }
}

struct EffectBindingValueDisplay<'a>(&'a EffType);

impl Display for EffectBindingValueDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        format_effect_binding_value(self.0, f)
    }
}

pub(crate) fn display_effect_binding_value(eff: &EffType) -> impl Display + '_ {
    EffectBindingValueDisplay(eff)
}

pub(crate) fn format_function_effect_suffix(
    eff: &EffType,
    f: &mut fmt::Formatter<'_>,
) -> fmt::Result {
    if eff.is_empty() {
        Ok(())
    } else {
        write!(f, " ! {}", display_effect_binding_value(eff))
    }
}

pub fn no_effects() -> EffType {
    EffType::empty()
}

pub fn effect(effect: PrimitiveEffect) -> EffType {
    EffType::single_primitive(effect)
}

pub fn effects(effects: &[PrimitiveEffect]) -> EffType {
    EffType::multiple_primitive(effects)
}

pub fn effect_read() -> EffType {
    effect(PrimitiveEffect::Read)
}

pub fn effect_write() -> EffType {
    effect(PrimitiveEffect::Write)
}

pub fn effects_read_write() -> EffType {
    effects(&[PrimitiveEffect::Read, PrimitiveEffect::Write])
}

pub fn effect_var(i: u32) -> EffType {
    EffType::single_variable(EffectVar::new(i))
}

pub fn effect_vars(vars: &[u32]) -> EffType {
    EffType::multiple_variable(&vars.iter().copied().map(EffectVar::new).collect::<Vec<_>>())
}

/// Instantiation substitution that maps effect variables to actual effects.
pub type EffectsInstSubst = FxHashMap<EffectVar, EffType>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constructions_and_destructions() {
        use PrimitiveEffect::*;
        type ET = EffType;
        type EV = EffectVar;

        assert_eq!(ET::empty(), ET::from_vec(vec![]));

        assert_eq!(
            ET::multiple_primitive(&[Read, Write]),
            ET::multiple_primitive(&[Write, Read])
        );
        assert_eq!(
            format!("{}", ET::multiple_primitive(&[Read, Write])),
            "read, write"
        );

        assert_eq!(
            ET::multiple_variable(&[EV::new(0), EV::new(1)]),
            ET::multiple_variable(&[EV::new(1), EV::new(0)])
        );
        assert_eq!(
            format!("{}", ET::multiple_variable(&[EV::new(0), EV::new(1)])),
            "e₀, e₁"
        );
    }

    #[test]
    fn instantiate_effects_uses_substitution_when_relevant() {
        use PrimitiveEffect::*;
        type ET = EffType;
        type EV = EffectVar;

        let effects = ET::from_vec(vec![
            Effect::Variable(EV::new(0)),
            Effect::Primitive(Read),
            Effect::Variable(EV::new(1)),
        ]);
        let mut subst = EffectsInstSubst::default();
        subst.insert(
            EV::new(1),
            ET::from_vec(vec![Effect::Primitive(Write), Effect::Primitive(Read)]),
        );

        assert_eq!(
            effects.instantiate(&subst),
            ET::from_vec(vec![
                Effect::Variable(EV::new(0)),
                Effect::Primitive(Read),
                Effect::Primitive(Write),
            ])
        );
        assert_eq!(effects.instantiate(&EffectsInstSubst::default()), effects);
    }

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn eff_type_is_compact_on_64_bit_targets() {
        assert_eq!(std::mem::size_of::<EffType>(), 16);
    }

    #[test]
    #[cfg(target_pointer_width = "32")]
    fn eff_type_is_compact_on_32_bit_targets() {
        assert_eq!(std::mem::size_of::<EffType>(), 8);
    }

    #[test]
    fn high_effect_variables_use_fallback_without_changing_set_behavior() {
        type ET = EffType;
        type EV = EffectVar;

        let effects = ET::multiple_variable(&[EV::new(63), EV::new(64), EV::new(1)]);

        assert!(effects.contains(Effect::Variable(EV::new(1))));
        assert!(effects.contains(Effect::Variable(EV::new(63))));
        assert!(effects.contains(Effect::Variable(EV::new(64))));
        assert_eq!(
            effects.inner_vars(),
            vec![EV::new(1), EV::new(63), EV::new(64)]
        );
        assert_eq!(format!("{effects}"), "e₁, e₆₃, e₆₄");
    }
}
