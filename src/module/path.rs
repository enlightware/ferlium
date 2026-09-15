// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use std::fmt::{self, Display};

use derive_new::new;
use ustr::Ustr;

use crate::{ast::UstrSpan, format::write_with_separator};

/// A non-spanned path used in HIR and module lookups.
#[derive(Debug, Clone, PartialEq, Eq, Hash, new)]

pub struct Path {
    pub segments: Vec<Ustr>,
}

impl Path {
    pub fn single(name: Ustr) -> Self {
        Self {
            segments: vec![name],
        }
    }
    pub fn single_str(name: &str) -> Self {
        Self {
            segments: vec![Ustr::from(name)],
        }
    }

    pub fn is_empty(&self) -> bool {
        self.segments.is_empty()
    }
    pub fn is_single_named_str(&self, name: &str) -> bool {
        self.segments.len() == 1 && self.segments[0] == name
    }

    pub fn from_ast_segments(segments: &[UstrSpan]) -> Self {
        Self {
            segments: segments.iter().map(|(name, _)| *name).collect(),
        }
    }
}

impl Display for Path {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_with_separator(self.segments.iter(), "::", f)
    }
}
