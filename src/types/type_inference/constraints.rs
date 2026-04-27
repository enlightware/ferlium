// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::fmt::{self, Display};

use crate::{
    format::FormatWith,
    module::ModuleEnv,
    parser::location::Location,
    types::{effects::EffType, mutability::MutType, r#type::Type, type_scheme::PubTypeConstraint},
};

/// A constraint on types.
#[derive(Debug, Clone)]
pub enum TypeConstraint {
    SameType {
        current: Type,
        current_span: Location,
        expected: Type,
        expected_span: Location,
    },
    SubType {
        current: Type,
        current_span: Location,
        expected: Type,
        expected_span: Location,
    },
    Pub(PubTypeConstraint),
}

impl FormatWith<ModuleEnv<'_>> for TypeConstraint {
    fn fmt_with(&self, f: &mut std::fmt::Formatter, env: &ModuleEnv<'_>) -> std::fmt::Result {
        use TypeConstraint::*;
        match self {
            SameType {
                current, expected, ..
            } => {
                write!(
                    f,
                    "{} = {}",
                    current.format_with(env),
                    expected.format_with(env)
                )
            }
            SubType {
                current, expected, ..
            } => {
                write!(
                    f,
                    "{} ≤ {}",
                    current.format_with(env),
                    expected.format_with(env)
                )
            }
            Pub(constraint) => constraint.fmt_with(f, env),
        }
    }
}

/// A constraint on mutability.
#[derive(Debug, Clone)]
pub enum MutConstraint {
    SameMut {
        current: MutType,
        current_span: Location,
        expected: MutType,
        expected_span: Location,
    },
    MutBeAtLeast {
        current: MutType,
        current_span: Location,
        target: MutType,
        reason_span: Location,
    },
}

impl Display for MutConstraint {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use MutConstraint::*;
        match self {
            SameMut {
                current, expected, ..
            } => write!(f, "{current} = {expected}"),
            MutBeAtLeast {
                current, target, ..
            } => write!(f, "{current} ≥ {target}"),
        }
    }
}

/// A constraint on effects.
#[derive(Debug, Clone)]
pub enum EffectConstraint {
    SameEffect {
        current: EffType,
        current_span: Location,
        expected: EffType,
        expected_span: Location,
    },
}

impl Display for EffectConstraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use EffectConstraint::*;
        match self {
            SameEffect {
                current, expected, ..
            } => write!(f, "{current} = {expected}"),
        }
    }
}
