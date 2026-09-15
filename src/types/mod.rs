// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

pub mod effects;
pub mod mutability;
pub mod r#trait;
pub mod trait_solver;
pub mod r#type;
pub(crate) mod type_properties;
pub mod type_scheme;
pub mod typing_env;

pub(crate) mod coherence;
pub(crate) mod never;
pub(crate) mod recursive_equation;
pub(crate) mod type_constraints;
pub(crate) mod type_inference;
pub(crate) mod type_like;
pub(crate) mod type_mapper;
pub(crate) mod type_scheme_display;
pub(crate) mod type_substitution;
pub mod type_visitor;
pub mod var_set;
