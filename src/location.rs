// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use std::ops::Range;

use crate::{define_id_type, format::FormatWith};

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

/// A location in the user's input, containing a span and a source ID.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct Location {
    span: Span,
    source_id: SourceId,
}

impl Location {
    /// Create a new location starting at byte `start` and ending at byte `end`,
    /// within the source identified by `source_id`.
    pub fn new(start: u32, end: u32, source_id: SourceId) -> Self {
        Location {
            span: Span::new(start, end),
            source_id,
        }
    }

    /// Create a new location starting at byte `start` and ending at byte `end`,
    /// within the source identified by `source_id`, taking byte index as usize.
    pub fn new_usize(start: usize, end: usize, source_id: SourceId) -> Self {
        Self::new(start as u32, end as u32, source_id)
    }

    /// Create a new location by fusing the spans of multiple locations.
    /// Panics if `others` are from different sources.
    pub fn fuse(locations: impl IntoIterator<Item = Self>) -> Option<Self> {
        let mut source_id: Option<SourceId> = None;
        let mut start = u32::MAX;
        let mut end = 0u32;
        for other in locations {
            if let Some(source_id) = source_id {
                let other_id = other.source_id;
                if other_id != source_id {
                    panic!(
                        "Cannot fuse locations from different sources: {source_id}:{:?} with {other_id}:{:?}",
                        start..end,
                        other.span.as_range()
                    );
                }
            } else {
                source_id = Some(other.source_id);
            }
            start = start.min(other.start());
            end = end.max(other.end());
        }
        source_id.map(|source_id| Self::new(start, end, source_id))
    }

    /// Byte offset of the start of the span.
    pub fn start(&self) -> u32 {
        self.span.start
    }

    /// Byte offset of the start of the span.
    pub fn start_usize(&self) -> usize {
        self.span.start as usize
    }

    /// Returns a location at the start of this location.
    pub fn start_location(&self) -> Self {
        Self::new(self.start(), self.start(), self.source_id)
    }

    /// Byte offset of the end of the span.
    pub fn end(&self) -> u32 {
        self.span.end
    }

    /// Byte offset of the end of the span.
    pub fn end_usize(&self) -> usize {
        self.span.end as usize
    }

    /// Returns a location at the end of this location.
    pub fn end_location(&self) -> Self {
        Self::new(self.end(), self.end(), self.source_id)
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

    /// Returns the source ID of this location.
    pub fn source_id(&self) -> SourceId {
        self.source_id
    }

    /// Returns a reference to the source ID of this location.
    pub fn source_id_ref(&self) -> &SourceId {
        &self.source_id
    }
}

/// A location that can be instantiated at a use site.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstantiableLocation {
    pub def_site: Option<Location>,
    pub use_site: Option<Location>,
}
impl InstantiableLocation {
    pub fn new(initial: Location) -> Self {
        Self {
            def_site: Some(initial),
            use_site: Some(initial),
        }
    }

    pub fn new_none() -> Self {
        Self {
            def_site: None,
            use_site: None,
        }
    }

    pub fn instantiate(&mut self, use_site: Location) {
        self.use_site = Some(use_site);
    }
}

impl FormatWith<SourceTable> for Location {
    fn fmt_with(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        source_table: &SourceTable,
    ) -> std::fmt::Result {
        let start = self.start_usize();
        let end = self.end_usize();
        let source_id = self.source_id();
        match source_table.get_source(source_id) {
            Some(source) => {
                let position = get_line_column(source, start);
                let snippet = &source[start..end];
                write!(
                    f,
                    "{}:{}:{}: `{}`",
                    source_id, position.0, position.1, snippet
                )
            }
            None => {
                write!(f, "#{}:{}..{}", source_id, start, end)
            }
        }
    }
}

define_id_type!(
    /// Source code ID within a source table
    SourceId
);

/// Table of source code strings for modules.
#[derive(Debug, Clone, Default)]
pub struct SourceTable {
    sources: Vec<(String, String)>,
}
impl SourceTable {
    pub fn add_source(&mut self, name: String, source: String) -> SourceId {
        let id = SourceId::from_index(self.sources.len());
        self.sources.push((name, source));
        id
    }

    pub fn get_source(&self, index: SourceId) -> Option<&String> {
        self.sources.get(index.as_index()).map(|(_, source)| source)
    }

    pub fn get_source_name(&self, index: SourceId) -> Option<&String> {
        self.sources.get(index.as_index()).map(|(name, _)| name)
    }
}

/// Get the line and column of a byte position in a string.
pub fn get_line_column(s: &str, byte_pos: usize) -> (usize, usize) {
    assert!(byte_pos <= s.len(), "byte_pos out of range");

    let s_up_to_pos = &s[..byte_pos];
    let line = s_up_to_pos.matches('\n').count() + 1;
    let last_newline_pos = s_up_to_pos.rfind('\n').map(|pos| pos + 1).unwrap_or(0);
    let col = s[last_newline_pos..byte_pos].chars().count() + 1;

    (line, col)
}
