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

/// Get the line and column of a byte position in a string.
pub fn get_line_column(s: &str, byte_pos: usize) -> (usize, usize) {
    assert!(byte_pos <= s.len(), "byte_pos out of range");

    let s_up_to_pos = &s[..byte_pos];
    let line = s_up_to_pos.matches('\n').count() + 1;
    let last_newline_pos = s_up_to_pos.rfind('\n').map(|pos| pos + 1).unwrap_or(0);
    let col = s[last_newline_pos..byte_pos].chars().count() + 1;

    (line, col)
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

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn test_get_line_column() {
        let text = "Hello\n世界\nRust";
        assert_eq!(get_line_column(text, 0), (1, 1));
        let byte_pos_o = text.find('o').unwrap();
        assert_eq!(get_line_column(text, byte_pos_o), (1, 5));
        let byte_pos_newline = text.find('\n').unwrap();
        assert_eq!(get_line_column(text, byte_pos_newline), (1, 6));
        let byte_pos_kanji = text.find('世').unwrap();
        assert_eq!(get_line_column(text, byte_pos_kanji), (2, 1));
        let byte_pos_kanji2 = text.find('界').unwrap();
        assert_eq!(get_line_column(text, byte_pos_kanji2), (2, 2));
        let byte_pos_rust = text.rfind('R').unwrap();
        assert_eq!(get_line_column(text, byte_pos_rust), (3, 1));
        let byte_pos_end = text.len();
        assert_eq!(get_line_column(text, byte_pos_end), (3, 5)); // "Rust" has 4 characters
    }
}
