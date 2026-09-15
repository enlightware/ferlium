// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use crate::{
    cached_ty,
    types::r#type::{Type, variant_type},
};

pub const ORDERING_LESS: &str = "Less";
pub const ORDERING_EQUAL: &str = "Equal";
pub const ORDERING_GREATER: &str = "Greater";

pub fn ordering_type() -> Type {
    cached_ty!(|| variant_type([
        (ORDERING_LESS, Type::unit()),
        (ORDERING_EQUAL, Type::unit()),
        (ORDERING_GREATER, Type::unit()),
    ]))
}

/// Rust body; the typed adapter encodes its result without exposing enums or Ferlium tags.
pub(crate) fn compare<T: Ord>(lhs: T, rhs: T) -> std::cmp::Ordering {
    lhs.cmp(&rhs)
}
