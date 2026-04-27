// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
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
