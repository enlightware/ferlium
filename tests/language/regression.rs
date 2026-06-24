// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use ustr::ustr;

use ferlium::compiler::error::CompilationErrorImpl;
use ferlium::hir::value::Value;
use ferlium::{Compiler, Path, eval::eval_node};
use test_log::test;

use indoc::indoc;

use crate::harness::{TestSession, int};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn ide_diagnostic_inside_multibyte_char_does_not_panic() {
    let mut compiler = Compiler::new();
    let errors = compiler.compile(indoc! { r#"
        fn
            let x = [1, 2,ion with unicode: λ ≈ ⇝
        fn display_name(user) {
            f"hello {user.name}"
        } main() {
            let x = [1, 2, ];
            x[
        }
    "# });

    assert!(errors.is_some());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn ide_empty_record_style_variant_constructor_does_not_panic() {
    let mut compiler = Compiler::new();
    let _ = compiler.compile("fMi {}\n");
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn constrained_function_value_arithmetic_does_not_panic() {
    let mut session = TestSession::new();
    session.compile("fn b(mut item) { item - map != map * map }");
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effect_polymorphic_function_parameter_arithmetic_does_not_panic() {
    let mut session = TestSession::new();
    session.compile("fn acc(a) { map + 0 == a + map; }");
}

// Previously, the ModuleParser (used for prelude/module-level code) had an LALR state-merge bug:
// when an `if` true-branch ended with a block-like expression (e.g. `match`), the parser would
// enter the expression-reduction chain (Sp<CastExpr<"">>) instead of producing Sp<Block>, causing
// it to miss the `else` and report: "expected one of "fn", "}", DOC_COMMENT, found "else"".
//
// Fixed by introducing `BranchBlock` as a separate non-terminal for if/for/loop bodies,
// preventing the spurious LALR state merge with the expression hierarchy.
//
// Note: the bug only affected ModuleParser (not ModuleAndBlockContentParser used for user code),
// so these user-code tests serve as documentation and regression guards for the pattern.
// `array_peek_back` is a generic native call the SSA interpreter cannot lower yet, so this stays
// HIR-only (emits `if_else_after_match_expression::hir`). Switch to `dual_test!` once SSA supports
// generic native calls.
hir_only_test!(if_else_after_match_expression {
    let mut session = TestSession::new();
    // `if cond { match ... } else { ... }` — true-branch ends with a match expression
    assert_val_eq!(
        session.run(indoc! { r#"
            fn first_or_zero(a: [int]) {
                if a[0] > 0 {
                    match array_peek_back(a) { Some(x) => x, None => 0 }
                } else {
                    0
                }
            }
            first_or_zero([42])
        "# }),
        int(42)
    );
    assert_val_eq!(
        session.run(indoc! { r#"
            fn first_or_zero(a: [int]) {
                if a[0] > 0 {
                    match array_peek_back(a) { Some(x) => x, None => 0 }
                } else {
                    0
                }
            }
            first_or_zero([-1])
        "# }),
        int(0)
    );
});

// `choose(flag)` is generic, which the SSA emitter cannot lower yet (generic values must move
// through a Value dictionary witness), so this stays HIR-only. Switch to `dual_test!` once SSA
// supports generic functions.
hir_only_test!(if_else_after_nested_block_expression {
    let mut session = TestSession::new();
    // `if cond { { ... } } else { ... }` — true-branch ends with a nested block
    assert_val_eq!(
        session.run(indoc! { r#"
            fn choose(flag) {
                if flag {
                    { 1 }
                } else {
                    2
                }
            }
            choose(true)
        "# }),
        int(1)
    );
    assert_val_eq!(
        session.run(indoc! { r#"
            fn choose(flag) {
                if flag {
                    { 1 }
                } else {
                    2
                }
            }
            choose(false)
        "# }),
        int(2)
    );
});

// Demonstrates a `dual_test!` that is green on BOTH backends: a fully concrete (monomorphic)
// snippet, so the SSA backend can lower it. Emits `concrete_if_else_runs_on_both_backends::hir`
// and `::ssa`.
dual_test!(concrete_if_else_runs_on_both_backends {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! { r#"
            fn choose(flag: bool) -> int {
                if flag {
                    { 1 }
                } else {
                    2
                }
            }
            choose(true)
        "# }),
        int(1)
    );
    assert_val_eq!(
        session.run(indoc! { r#"
            fn choose(flag: bool) -> int {
                if flag {
                    { 1 }
                } else {
                    2
                }
            }
            choose(false)
        "# }),
        int(2)
    );
});

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_iterator() {
    let mut session = TestSession::new();
    assert_val_eq!(
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
    assert_val_eq!(
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
    assert_val_eq!(
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
    assert_val_eq!(
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
    assert_val_eq!(
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
fn value_to_string_arrays_by_logical_contents() {
    let mut session = TestSession::new();
    let module_and_expr = session.compile("[{ a: 1 }, { a: 2 }]");
    let expr = module_and_expr
        .expr
        .expect("expected an expression for the formatting regression");
    let value = {
        let compiler_session = session.session();
        let module = compiler_session.expect_fresh_module(module_and_expr.module_id);
        eval_node(
            &module.hir_arena,
            expr.expr,
            module_and_expr.module_id,
            &expr.locals,
            compiler_session,
        )
        .unwrap()
        .into_value()
    };
    assert_eq!(
        session.value_to_string(module_and_expr.module_id, value, expr.ty.ty),
        "[{ a: 1 }, { a: 2 }]"
    );

    let module_and_expr = session.compile("[[1, 2], [3, 4]]");
    let expr = module_and_expr
        .expr
        .expect("expected an expression for the formatting regression");
    let value = {
        let compiler_session = session.session();
        let module = compiler_session.expect_fresh_module(module_and_expr.module_id);
        eval_node(
            &module.hir_arena,
            expr.expr,
            module_and_expr.module_id,
            &expr.locals,
            compiler_session,
        )
        .unwrap()
        .into_value()
    };
    assert_eq!(
        session.value_to_string(module_and_expr.module_id, value, expr.ty.ty),
        "[[1, 2], [3, 4]]"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn join_empty_sequence_compiles_repeatedly_in_shared_session() {
    let mut session = ferlium::CompilerSession::new();
    for name in ["repl0", "repl1", "repl2"] {
        session
            .compile("join([], \",\")", name, Path::single_str(name))
            .unwrap_or_else(|error| panic!("Compilation error in {name}: {error:?}"));
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn unresolved_expression_constraints_do_not_reach_dictionary_passing() {
    let mut session = TestSession::new();
    session
        .fail_compilation("[] == 0()")
        .expect_unbound_ty_var();
    session
        .fail_compilation("0() and (a != a)")
        .expect_unbound_ty_var();
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_trait_improvement_probe_from_grammar_fuzzer_does_not_overflow_stack() {
    let mut session = TestSession::new();
    session
        .fail_compilation("{filter_map} - 0[0] == 0")
        .expect_unbound_ty_var();
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn inferred_function_value_derivation_from_grammar_fuzzer_does_not_panic() {
    let mut session = TestSession::new();
    let error = session
        .fail_compilation("|a| a = for a in [] { a() }")
        .into_inner();
    match error {
        CompilationErrorImpl::TraitImplNotFound { trait_ref, .. } => {
            assert_eq!(trait_ref, "Value");
        }
        other => panic!("expected TraitImplNotFound for Value, got {other:?}"),
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_function_effect_equality_from_grammar_fuzzer_does_not_overflow_stack() {
    let mut session = TestSession::new();
    let error = session
        .fail_compilation(
            "fn a<map, a>(a: a) { \
                let mut result: None(a, [()]) | Some = a(); \
                let b: result = a < a or a; \
            }",
        )
        .into_inner();
    match error {
        CompilationErrorImpl::TypeMismatch { .. } => {}
        other => panic!("expected TypeMismatch, got {other:?}"),
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_function_trait_improvement_slow_unit_from_grammar_fuzzer_finishes() {
    let mut session = TestSession::new();
    session.fail_compilation(
        "filter_map * filter_map \
            - filter_map * filter_map * filter_map \
            - filter_map \
            + filter_map * filter_map \
            == filter_map * filter_map * filter_map * filter_map \
                * filter_map * filter_map * filter_map * filter_map \
            or 0 < 0",
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_function_trait_improvement_timeout_from_grammar_fuzzer_finishes() {
    let mut session = TestSession::new();
    session.fail_compilation(
        "3.result == -map \
            and map + map + map + map + map + map + map * 0.a.a \
                == map * map + map + map + map + 0 + 0 + 42(-y())",
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn repeated_generic_function_effect_normalization_from_grammar_fuzzer_finishes() {
    let mut session = TestSession::new();
    session.fail_compilation(
        "map + map + map + map + map + x \
            + {acc, map}.map.map(map == map) + map \
            < map + map + map + map + map + map + map + map \
            and a - 0 + 0 + 0 + 0 == 0",
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn returned_lambda_with_function_typed_num_constraint_compiles() {
    let mut session = TestSession::new();
    session.compile("pub fn b() { || 0() }");
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn broad_generic_alias_does_not_recurse_while_formatting_error() {
    let mut session = TestSession::new();
    session
        .fail_compilation(indoc! { r#"
            type Account<a> = a;
            fn b() -> {} {}
        "# })
        .expect_type_mismatch("()", "{  }");
}

// A `break` whose value itself diverges (e.g. `break return x`) terminates the current block while
// lowering that value. The `break` handler must then skip its own unwind / `stack_restore` / jump
// to the loop exit, otherwise the SSA emitter panics with "insertion after terminator".
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn break_with_diverging_value_does_not_insert_after_terminator() {
    let mut session = TestSession::new();

    // The break value is a bare `return`: the block is terminated by the `ret`.
    assert_val_eq!(
        session.run("fn run() -> int { loop { break return 7 } } run()"),
        int(7)
    );

    // Several iterations (driven by `continue`) before the diverging `break return`.
    assert_val_eq!(
        session.run(indoc! { r#"
            fn run() -> int {
                let mut i = 0;
                loop {
                    i += 1;
                    if i < 3 { continue };
                    break return i
                }
            }
            run()
        "# }),
        int(3)
    );

    // The break value only diverges on one branch: when it falls through with a real value, the
    // block is *not* terminated and the guard must still emit the jump to the loop exit.
    assert_val_eq!(
        session.run("fn run() -> int { let c = false; loop { break if c { return 1 } else { 2 } } } run()"),
        int(2)
    );
    assert_val_eq!(
        session.run("fn run() -> int { let c = true; loop { break if c { return 1 } else { 2 } } } run()"),
        int(1)
    );
}
