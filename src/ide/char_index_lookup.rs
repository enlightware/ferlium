// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
/// Data structure to map byte indices to character indices in a string.
#[derive(Default)]
pub struct CharIndexLookup {
    // for each byte index, stores the corresponding character index
    char_indices: Vec<usize>,
    // the character index of the next character past the string
    next_char_index: usize,
}

impl CharIndexLookup {
    pub fn new(s: &str) -> Self {
        let len = s.len();
        let mut char_indices = vec![0; len];
        let mut char_index = 0;
        let mut i = 0;
        for (byte_index, _) in s.char_indices() {
            // write last char
            while i < byte_index {
                char_indices[i] = char_index - 1;
                i += 1;
            }
            char_index += 1;
        }
        // write last char
        while i < len {
            char_indices[i] = char_index - 1;
            i += 1;
        }
        Self {
            char_indices,
            next_char_index: char_index,
        }
    }

    /// Return the character index corresponding to the given byte index, and the size last character index + 1 otherwise.
    pub fn byte_to_char_position(&self, byte_index: usize) -> usize {
        if byte_index < self.char_indices.len() {
            self.char_indices[byte_index]
        } else {
            self.next_char_index
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
    fn test_char_index_lookup() {
        let s = "éaé";
        let lookup = CharIndexLookup::new(s);
        assert_eq!(lookup.byte_to_char_position(0), 0);
        assert_eq!(lookup.byte_to_char_position(1), 0);
        assert_eq!(lookup.byte_to_char_position(2), 1);
        assert_eq!(lookup.byte_to_char_position(3), 2);
        assert_eq!(lookup.byte_to_char_position(4), 2);
    }
}
