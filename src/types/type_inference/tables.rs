// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use ena::unify::{EqUnifyValue, UnifyKey, UnifyValue};

use crate::types::{
    effects::{EffType, EffectVarKey},
    mutability::{MutVal, MutVarKey},
    r#type::{TyVarKey, Type},
};

impl UnifyKey for TyVarKey {
    type Value = Option<Type>;

    fn index(&self) -> u32 {
        self.name()
    }

    fn from_index(u: u32) -> Self {
        Self::new(u)
    }

    fn tag() -> &'static str {
        "TyVarKey"
    }
}

impl EqUnifyValue for Type {}

impl UnifyKey for MutVarKey {
    type Value = Option<MutVal>;

    fn index(&self) -> u32 {
        self.name()
    }

    fn from_index(u: u32) -> Self {
        Self::new(u)
    }

    fn tag() -> &'static str {
        "MutVarKey"
    }
}

impl EqUnifyValue for MutVal {}

impl UnifyKey for EffectVarKey {
    type Value = Option<EffType>;

    fn index(&self) -> u32 {
        self.name()
    }

    fn from_index(u: u32) -> Self {
        Self::new(u)
    }

    fn tag() -> &'static str {
        "EffectVarKey"
    }
}

/// Effects can always be unified through the union operation.
impl UnifyValue for EffType {
    type Error = ena::unify::NoError;

    fn unify_values(a: &Self, b: &Self) -> Result<Self, Self::Error> {
        Ok(a.union(b))
    }
}
