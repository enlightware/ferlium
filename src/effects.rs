use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
};

use enum_as_inner::EnumAsInner;

use crate::format::{type_variable_subscript, write_with_separator};

/// An effect describing the non-pure behavior of a function
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PrimitiveEffect {
    Read,
    Write,
}

impl Display for PrimitiveEffect {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use PrimitiveEffect::*;
        match self {
            Read => write!(f, "read"),
            Write => write!(f, "write"),
        }
    }
}

/// A generic variable for effects
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EffectVar {
    /// The name of this effect variable, its identity in the context considered
    name: u32,
}

impl EffectVar {
    pub fn new(name: u32) -> Self {
        Self { name }
    }
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

/// An effects type, consisting of a set of effects.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EffType(Vec<Effect>);
impl EffType {
    pub fn empty() -> Self {
        Self::default()
    }
    pub fn single(effect: Effect) -> Self {
        Self(vec![effect])
    }
    pub fn single_primitive(effect: PrimitiveEffect) -> Self {
        Self::single(Effect::Primitive(effect))
    }
    pub fn single_variable(var: EffectVar) -> Self {
        Self::single(Effect::Variable(var))
    }
    pub fn multiple(effects: &[Effect]) -> Self {
        Self::from_vec(effects.to_vec())
    }
    pub fn multiple_primitive(effects: &[PrimitiveEffect]) -> Self {
        Self::from_vec(effects.iter().copied().map(Effect::Primitive).collect())
    }
    pub fn multiple_variable(vars: &[EffectVar]) -> Self {
        Self::from_vec(vars.iter().copied().map(Effect::Variable).collect())
    }

    pub fn from_vec(effects: Vec<Effect>) -> Self {
        let mut effects = effects;
        effects.sort();
        effects.dedup();
        Self(effects)
    }

    pub fn insert(&mut self, effect: Effect) {
        self.0.push(effect);
        self.0.sort();
        self.0.dedup();
    }

    pub fn extend(&mut self, other: &Self) {
        self.0.extend(other.0.iter());
        self.0.sort();
        self.0.dedup();
    }

    pub fn union(&self, other: &Self) -> Self {
        let mut new = self.clone();
        new.0.extend(other.0.iter());
        new.0.sort();
        new.0.dedup();
        new
    }

    pub fn to_single_variable(&self) -> Option<EffectVar> {
        if self.0.len() == 1 {
            match self.0.first().unwrap() {
                Effect::Variable(var) => Some(*var),
                _ => None,
            }
        } else {
            None
        }
    }

    pub fn is_only_vars(&self) -> bool {
        self.0
            .iter()
            .all(|effect| matches!(effect, Effect::Variable(_)))
    }

    pub fn to_multiple_vars(&self) -> Option<Vec<EffectVar>> {
        if self.is_only_vars() {
            Some(
                self.0
                    .iter()
                    .map(|effect| match effect {
                        Effect::Variable(var) => *var,
                        _ => unreachable!(),
                    })
                    .collect(),
            )
        } else {
            None
        }
    }

    pub fn any(&self) -> bool {
        !self.0.is_empty()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn contains(&self, effect: Effect) -> bool {
        self.0.contains(&effect)
    }

    pub fn iter(&self) -> impl Iterator<Item = &Effect> {
        self.0.iter()
    }

    pub fn as_single(&self) -> Option<Effect> {
        if self.0.len() == 1 {
            Some(*self.0.first().unwrap())
        } else {
            None
        }
    }

    pub fn fill_with_inner_effect_vars(&self, vars: &mut HashSet<EffectVar>) {
        for effect in self.0.iter() {
            match effect {
                Effect::Primitive(_) => {}
                Effect::Variable(var) => {
                    vars.insert(*var);
                }
            }
        }
    }

    pub fn instantiate(&self, subst: &EffectsSubstitution) -> Self {
        let effects = self
            .0
            .iter()
            .flat_map(|effect| {
                match effect {
                    Effect::Primitive(effect) => EffType::single_primitive(*effect),
                    Effect::Variable(var) => match subst.get(var) {
                        Some(subst) => subst.clone(),
                        None => EffType::single(*effect),
                    },
                }
                .into_iter()
            })
            .collect();
        Self::from_vec(effects)
    }
}

impl IntoIterator for EffType {
    type Item = Effect;
    type IntoIter = std::vec::IntoIter<Effect>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl FromIterator<Effect> for EffType {
    fn from_iter<T: IntoIterator<Item = Effect>>(iter: T) -> Self {
        Self::from_vec(iter.into_iter().collect::<Vec<_>>())
    }
}

impl Display for EffType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write_with_separator(self.0.iter(), ", ", f)
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

pub type EffectsSubstitution = HashMap<EffectVar, EffType>;

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
}
