/// Apply Rust-style string escapes to a string.
pub(crate) fn apply_string_escapes(s: &str) -> String {
    let mut result = String::new();
    let mut chars = s.chars().peekable();

    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some('n') => result.push('\n'),
                Some('t') => result.push('\t'),
                Some('r') => result.push('\r'),
                Some('\\') => result.push('\\'),
                Some('"') => result.push('"'),
                Some('0') => result.push('\0'),
                Some('x') => {
                    // Handle \xNN (hexadecimal byte)
                    let mut hex = String::new();
                    for _ in 0..2 {
                        if let Some(h) = chars.next() {
                            hex.push(h);
                        } else {
                            break;
                        }
                    }
                    if let Ok(byte) = u8::from_str_radix(&hex, 16) {
                        result.push(byte as char);
                    } else {
                        // Invalid hex escape, keep as-is
                        result.push_str("\\x");
                        result.push_str(&hex);
                    }
                }
                Some('u') => {
                    // Handle \u{N} to \u{NNNNNN} (Unicode code point)
                    if chars.next() == Some('{') {
                        let mut hex = String::new();
                        for h in chars.by_ref() {
                            if h == '}' {
                                break;
                            } else {
                                hex.push(h);
                            }
                        }
                        if let Ok(cp) = u32::from_str_radix(&hex, 16) {
                            if let Some(ch) = std::char::from_u32(cp) {
                                result.push(ch);
                            } else {
                                // Invalid Unicode code point
                                result.push_str("\\u{");
                                result.push_str(&hex);
                                result.push('}');
                            }
                        } else {
                            // Invalid hex number
                            result.push_str("\\u{");
                            result.push_str(&hex);
                            result.push('}');
                        }
                    } else {
                        // Invalid Unicode escape, keep as-is
                        result.push_str("\\u");
                    }
                }
                Some(other) => {
                    // Unknown escape sequence, keep as-is
                    result.push('\\');
                    result.push(other);
                }
                None => {
                    // Trailing backslash, keep as-is
                    result.push('\\');
                }
            }
        } else {
            result.push(c);
        }
    }

    result
}
