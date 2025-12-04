// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use std::ops::Range;

use ustr::{Ustr, ustr};

use crate::{format::FormatWith, module::ModuleEnv};

/// A range of bytes in the user's input.
/// It only contains the start and end byte offsets, not the actual input string.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub fn new(start: u32, end: u32) -> Self {
        if end < start {
            panic!("Span starts ({start}) after it ends ({end})!");
        }
        Span { start, end }
    }

    pub fn start(&self) -> u32 {
        self.start
    }

    pub fn start_usize(&self) -> usize {
        self.start as usize
    }

    pub fn end(&self) -> u32 {
        self.end
    }

    pub fn end_usize(&self) -> usize {
        self.end as usize
    }

    pub fn len(&self) -> u32 {
        self.end - self.start
    }

    pub fn as_range(&self) -> Range<usize> {
        self.start as usize..self.end as usize
    }
}

/// An external location is a span in a different module.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct ExternalLocation {
    module_name: Ustr,
    span: Span,
}

impl ExternalLocation {
    pub fn module_name(&self) -> Ustr {
        self.module_name
    }

    pub fn span(&self) -> Span {
        self.span
    }
}

/// A location in the user's input.
/// If it originated outside the current module, the module field tracks that original location,
/// and span tracks the location within the current module where it was brought into scope.
/// (the function instantiation point).
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct Location {
    span: Span,
    module: Option<ExternalLocation>,
}

impl Location {
    /// Create a new location starting at byte `start` and ending at byte `end`.
    pub fn new(start: u32, end: u32, module: Option<ExternalLocation>) -> Self {
        Location {
            span: Span::new(start, end),
            module,
        }
    }

    /// Create a new location starting at byte `start` and ending at byte `end`, in the current module.
    /// Panics if `end` is less than `start`.
    pub fn new_local(start: u32, end: u32) -> Self {
        Self::new(start, end, None)
    }

    pub fn new_local_usize(start: usize, end: usize) -> Self {
        Self::new(start as u32, end as u32, None)
    }

    /// Create a new location by fusing the spans of multiple locations.
    /// Panics if `others` is empty or are from different modules.
    pub fn fuse_range(others: impl IntoIterator<Item = Self>) -> Option<Self> {
        let mut module: Option<Option<ExternalLocation>> = None;
        let mut start = u32::MAX;
        let mut end = 0u32;
        for other in others {
            if let Some(module) = module {
                let self_name = module.map(|m| m.module_name);
                let other_name = other.module.map(|m| m.module_name);
                if self_name != other_name {
                    let self_name = self_name.unwrap_or(ustr("<current module>"));
                    let other_name = other_name.unwrap_or(ustr("<current module>"));
                    panic!(
                        "Cannot fuse locations from different modules: {self_name}:{:?} with {other_name}:{:?}",
                        start..end,
                        other.span.as_range()
                    );
                }
            } else {
                module = Some(other.module);
            }
            start = start.min(other.start());
            end = end.max(other.end());
        }
        module.map(|module| Self::new(start, end, module))
    }

    /// Byte offset of the start of the span.
    pub fn start(&self) -> u32 {
        self.span.start
    }

    /// Byte offset of the start of the span.
    pub fn start_usize(&self) -> usize {
        self.span.start as usize
    }

    /// Byte offset of the end of the span.
    pub fn end(&self) -> u32 {
        self.span.end
    }

    /// Byte offset of the end of the span.
    pub fn end_usize(&self) -> usize {
        self.span.end as usize
    }

    /// Length in bytes of the span.
    pub fn len(&self) -> u32 {
        self.span.end - self.span.start
    }

    /// Returns `true` if this location's span covers 0 bytes, or `false` otherwise.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the span of this location.
    pub fn span(&self) -> Span {
        self.span
    }

    /// Returns a range suitable for slicing strings.
    pub fn as_range(&self) -> Range<usize> {
        self.span.as_range()
    }

    /// Returns the module this location comes from, if any.
    pub fn module(&self) -> Option<ExternalLocation> {
        self.module
    }

    /// If module is not None, this location is in a different module, make it
    /// an imported location.
    pub fn instantiate(&mut self, module: Option<Ustr>, span: Span) {
        let name = match module {
            Some(name) => name,
            None => return,
        };
        if self.module.is_none() {
            // if the location was previously local, make it external
            self.module = Some(ExternalLocation {
                module_name: name,
                span: self.span, // The original span
            });
        }
        // Note: if the location was already external, just overwrite the instantiation point
        self.span = span; // The span of the instantiation point in the current module
    }
}

impl FormatWith<ModuleEnv<'_>> for Location {
    fn fmt_with(&self, f: &mut std::fmt::Formatter<'_>, env: &ModuleEnv<'_>) -> std::fmt::Result {
        if let Some(location) = self.module {
            match env.others.get(&location.module_name) {
                None => {
                    write!(
                        f,
                        "{}..{} in unknown imported module \"{}\"",
                        location.span.start(),
                        location.span.end(),
                        location.module_name
                    )
                }
                Some(module) => {
                    if let Some(source) = module.source.as_ref() {
                        write!(f, "{}", &source[location.span.as_range()])
                    } else {
                        write!(
                            f,
                            "{}..{} in imported module \"{}\"",
                            location.span.start(),
                            location.span.end(),
                            location.module_name
                        )
                    }
                }
            }
        } else if let Some(source) = env.current.source.as_ref() {
            write!(f, "{}", &source[self.span.as_range()])
        } else {
            write!(f, "{}..{} in current module", self.start(), self.end())
        }
    }
}
