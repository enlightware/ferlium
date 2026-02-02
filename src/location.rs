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
    pub(crate) source_id: SourceId,
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

    /// Create a new synthesized location with span 0..0 and source ID 0.
    pub fn new_synthesized() -> Self {
        Self::new(0, 0, SourceId::from_index(0))
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

    /// Returns `true` if this location is synthesized (source ID 0 and empty span).
    pub fn is_synthesized(&self) -> bool {
        self.source_id.as_index() == 0 && self.is_empty()
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
    pub def_site: Location,
    pub use_site: Location,
}
impl InstantiableLocation {
    pub fn new(initial: Location) -> Self {
        Self {
            def_site: initial,
            use_site: initial,
        }
    }

    pub fn new_synthesized() -> Self {
        Self {
            def_site: Location::new_synthesized(),
            use_site: Location::new_synthesized(),
        }
    }

    pub fn instantiate(&mut self, use_site: Location) {
        self.use_site = use_site;
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
        match source_table.get_source_entry(source_id) {
            Some(source) => {
                let position = source.get_line_column(start);
                let snippet = &source.source()[start..end];
                write!(
                    f,
                    "{}:{}:{}: `{}`",
                    source.name(),
                    position.0,
                    position.1,
                    snippet
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

/// An entry in the source table, containing a name and the source code string.
#[derive(Debug, Clone, Default)]
pub struct SourceEntry {
    name: String,
    source: String,
    line_starts: Vec<usize>,
}
impl SourceEntry {
    /// Create a new source entry with the given name and source code.
    /// It also computes the starting byte positions of each line in the source code.
    pub fn new(name: String, source: String) -> Self {
        let mut line_starts = vec![0];
        for (i, c) in source.char_indices() {
            if c == '\n' {
                line_starts.push(i + 1);
            }
        }
        Self {
            name,
            source,
            line_starts,
        }
    }

    pub fn name(&self) -> &String {
        &self.name
    }

    pub fn source(&self) -> &String {
        &self.source
    }

    /// Get the line and column (unicode scalar value) of a byte position in this source entry.
    pub fn get_line_column(&self, byte_pos: usize) -> (usize, usize) {
        let s = &self.source;
        assert!(byte_pos <= s.len(), "byte_pos out of range");

        // Binary search to find which line this byte position is on.
        // line_starts contains the byte position of the start of each line.
        let line = match self.line_starts.binary_search(&byte_pos) {
            Ok(idx) => idx + 1, // Exact match: byte_pos is the start of a line
            Err(idx) => idx, // Not found: position is between line_starts[idx-1] and line_starts[idx]
        };

        // Get the byte position where this line starts
        let line_start = self.line_starts[line - 1];

        // Calculate column by counting UTF-8 characters from line start to byte_pos
        let col = s[line_start..byte_pos].chars().count() + 1;

        (line, col)
    }
}

/// Table of source code strings for modules.
#[derive(Debug, Clone)]
pub struct SourceTable {
    sources: Vec<SourceEntry>,
}
impl SourceTable {
    pub fn add_source(&mut self, name: String, source: String) -> SourceId {
        let id = SourceId::from_index(self.sources.len());
        self.sources.push(SourceEntry::new(name, source));
        id
    }

    pub fn get_source_entry(&self, index: SourceId) -> Option<&SourceEntry> {
        self.sources.get(index.as_index())
    }

    pub fn get_source_text(&self, index: SourceId) -> Option<&String> {
        self.sources
            .get(index.as_index())
            .map(|entry| &entry.source)
    }

    pub fn get_source_name(&self, index: SourceId) -> Option<&String> {
        self.sources.get(index.as_index()).map(|entry| &entry.name)
    }

    pub fn get_latest_source_by_name(&self, name: &str) -> Option<(SourceId, &SourceEntry)> {
        for (i, entry) in self.sources.iter().enumerate().rev() {
            if entry.name == name {
                return Some((SourceId::from_index(i), entry));
            }
        }
        None
    }

    /// Get the line and column (unicode scalar value) of a byte position in a given source.
    pub fn get_line_column(&self, index: SourceId, byte_pos: usize) -> (usize, usize) {
        match self.sources.get(index.as_index()) {
            Some(source) => source.get_line_column(byte_pos),
            None => (0, 0),
        }
    }
}

impl Default for SourceTable {
    fn default() -> Self {
        let entry = SourceEntry::new("<synthesized>".into(), "".into());
        SourceTable {
            sources: vec![entry],
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[cfg(target_arch = "wasm32")]
    use wasm_bindgen_test::wasm_bindgen_test;

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn source_entry_get_line_column() {
        let entry = SourceEntry::new("test".into(), "Hello\n世界\nRust".into());
        assert_eq!(entry.get_line_column(0), (1, 1));
        let byte_pos_o = entry.source.find('o').unwrap();
        assert_eq!(entry.get_line_column(byte_pos_o), (1, 5));
        let byte_pos_newline = entry.source.find('\n').unwrap();
        assert_eq!(entry.get_line_column(byte_pos_newline), (1, 6));
        let byte_pos_kanji = entry.source.find('世').unwrap();
        assert_eq!(entry.get_line_column(byte_pos_kanji), (2, 1));
        let byte_pos_kanji2 = entry.source.find('界').unwrap();
        assert_eq!(entry.get_line_column(byte_pos_kanji2), (2, 2));
        let byte_pos_rust = entry.source.rfind('R').unwrap();
        assert_eq!(entry.get_line_column(byte_pos_rust), (3, 1));
        let byte_pos_end = entry.source.len();
        assert_eq!(entry.get_line_column(byte_pos_end), (3, 5)); // "Rust" has 4 characters
    }
}
