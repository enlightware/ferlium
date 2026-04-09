// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use ustr::ustr;

use ferlium::eval::eval_node;
use ferlium::value::Value;
use test_log::test;

use indoc::indoc;

use crate::harness::{TestSession, int};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_iterator() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run(indoc! { r#"
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
    let mut session = TestSession::new();
    assert_eq!(
        session.run(indoc! { r#"
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
    let mut session = TestSession::new();
    assert_eq!(
        session.run(indoc! { r#"
			enum Action { Quit }

			Action::Quit
		"# }),
        Value::raw_variant(ustr("Quit"), Value::unit())
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn never_in_if_branches() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run(indoc! { r#"
            fn unwrap(v) {
                match v {
                    None => abort(),
                    Some(x) => x
                }
            }

            unwrap(Some(1))
		"# }),
        int(1)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn never_in_if_branches_after_value_branch() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run(indoc! { r#"
            fn unwrap(v) {
                match v {
                    Some(x) => x,
                    None => abort()
                }
            }

            unwrap(Some(1))
        "# }),
        int(1)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn pretty_print_unknown_variant_with_named_payload_does_not_crash() {
    let mut session = TestSession::new();
    let module_and_expr =
        session.compile("[1, 2, 3] |> iter() |> map(|x| x as float) |> missing_collect()");
    let expr = module_and_expr
        .expr
        .expect("expected an expression for the pretty-print regression");
    let module = session
        .session()
        .expect_fresh_module(module_and_expr.module_id);
    let value = eval_node(
        &module.ir_arena,
        expr.expr,
        module_and_expr.module_id,
        &expr.locals,
        session.session(),
    )
    .unwrap()
    .into_value();
    let formatted = value.display_pretty(&expr.ty.ty).to_string();
    assert!(formatted.starts_with("missing_collect (MapIterator { "));
}
