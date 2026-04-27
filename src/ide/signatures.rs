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

/// A function signature data struct to be used in IDEs
#[cfg_attr(target_arch = "wasm32", wasm_bindgen(getter_with_clone))]
pub struct FunctionSignature {
    pub name: String,
    pub args: Vec<String>,
    pub doc: Option<String>,
}

pub(super) fn remove_effects(signature: &str) -> &str {
    let mut paren_depth = 0usize;
    let mut bracket_depth = 0usize;
    let mut brace_depth = 0usize;
    let mut angle_depth = 0usize;
    let mut bang_at_toplevel = None;

    for (index, ch) in signature.char_indices() {
        match ch {
            '(' => paren_depth += 1,
            ')' => paren_depth = paren_depth.saturating_sub(1),
            '[' => bracket_depth += 1,
            ']' => bracket_depth = bracket_depth.saturating_sub(1),
            '{' => brace_depth += 1,
            '}' => brace_depth = brace_depth.saturating_sub(1),
            '<' => angle_depth += 1,
            '>' => angle_depth = angle_depth.saturating_sub(1),
            '!' if paren_depth == 0
                && bracket_depth == 0
                && brace_depth == 0
                && angle_depth == 0 =>
            {
                bang_at_toplevel = Some(index);
            }
            _ => {}
        }
    }

    match bang_at_toplevel {
        Some(index) => signature[..index].trim(),
        None => signature.trim(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn remove_effects_ignores_nested_function_effects() {
        assert_eq!(
            remove_effects("((int) -> int ! read) -> int"),
            "((int) -> int ! read) -> int"
        );
        assert_eq!(
            remove_effects("((int) -> int ! read) -> int ! write"),
            "((int) -> int ! read) -> int"
        );
    }
}
