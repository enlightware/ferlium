// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

pub mod constraints;
pub mod defaulting;
pub mod effect_solver;
mod evidence_uses;
pub mod expr;
mod ground_bounds;
mod selection;
pub(crate) mod signature;
pub mod substitution;
pub mod tables;
mod type_bounds;
pub mod unify;
