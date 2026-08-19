// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
#[cfg(target_arch = "wasm32")]
use wasm_bindgen::prelude::*;

/// Encoding used for absolute text positions returned by the IDE API.
///
/// Rust compiler spans are UTF-8 byte offsets. Native IDE clients historically use Unicode scalar
/// offsets, whereas JavaScript editors such as CodeMirror use UTF-16 code-unit offsets.
#[cfg_attr(target_arch = "wasm32", wasm_bindgen)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum PositionEncoding {
    #[default]
    UnicodeScalar,
    Utf16CodeUnit,
}

/// Maps UTF-8 byte indices in a Rust string to the configured IDE position encoding.
#[derive(Default)]
pub struct PositionIndexLookup {
    // For each byte index, stores the encoded position at the start of that scalar value.
    indices: Vec<usize>,
    // The encoded position immediately past the string.
    end_index: usize,
}

impl PositionIndexLookup {
    pub fn new(s: &str, encoding: PositionEncoding) -> Self {
        let mut indices = vec![0; s.len()];
        let mut index = 0;
        for (byte_index, character) in s.char_indices() {
            indices[byte_index..byte_index + character.len_utf8()].fill(index);
            index += match encoding {
                PositionEncoding::UnicodeScalar => 1,
                PositionEncoding::Utf16CodeUnit => character.len_utf16(),
            };
        }
        Self {
            indices,
            end_index: index,
        }
    }

    /// Returns the encoded position containing `byte_index`, or the end position when past the text.
    pub fn byte_to_position(&self, byte_index: usize) -> usize {
        if byte_index < self.indices.len() {
            self.indices[byte_index]
        } else {
            self.end_index
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
    fn maps_utf8_bytes_to_unicode_scalars_by_default() {
        let lookup = PositionIndexLookup::new("é😀a", PositionEncoding::UnicodeScalar);

        assert_eq!(lookup.byte_to_position(0), 0);
        assert_eq!(lookup.byte_to_position(1), 0);
        assert_eq!(lookup.byte_to_position(2), 1);
        assert_eq!(lookup.byte_to_position(5), 1);
        assert_eq!(lookup.byte_to_position(6), 2);
        assert_eq!(lookup.byte_to_position(7), 3);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn maps_utf8_bytes_to_utf16_code_units() {
        let lookup = PositionIndexLookup::new("é😀a", PositionEncoding::Utf16CodeUnit);

        assert_eq!(lookup.byte_to_position(0), 0);
        assert_eq!(lookup.byte_to_position(1), 0);
        assert_eq!(lookup.byte_to_position(2), 1);
        assert_eq!(lookup.byte_to_position(3), 1);
        assert_eq!(lookup.byte_to_position(4), 1);
        assert_eq!(lookup.byte_to_position(5), 1);
        assert_eq!(lookup.byte_to_position(6), 3);
        assert_eq!(lookup.byte_to_position(7), 4);
    }
}
