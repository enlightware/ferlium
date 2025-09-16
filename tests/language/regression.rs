// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use ustr::ustr;

use ferlium::value::Value;
use test_log::test;

use indoc::indoc;

use crate::common::{int, run};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_iterator() {
    assert_eq!(
        run(indoc! { r#"
			fn it(x) {
				for i in x { }
			}

			it([1.0, 2.0])
		"# }),
        Value::unit()
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn count_some_bug_minimized() {
    assert_eq!(
        run(indoc! { r#"
		fn count_some(a: [None | Some(int)]) {
			let mut sum = 0;
			for option in a {
				match option {
					Some(v) => sum = sum + 1,
					None => ()
				}
			};
			sum
		}

		count_some([Some(1), None, Some(2), Some(3), None, Some(4)])
	"# }),
        int(4)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn enum_constructors() {
    assert_eq!(
        run(indoc! { r#"
			enum Action { Quit }

			Action::Quit
		"# }),
        Value::raw_variant(ustr("Quit"), Value::unit())
    );
}
