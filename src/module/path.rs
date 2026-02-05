// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use std::fmt::{self, Display};

use derive_new::new;
use ustr::Ustr;

use crate::format::write_with_separator;

/// A non-spanned path used in IR and module lookups.
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

    pub fn from_ast_segments(segments: &[crate::ast::UstrSpan]) -> Self {
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
