// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use ustr::ustr;

use ferlium::compiler::error::{CompilationErrorImpl, MutabilityMustBeWhat};
use ferlium::hir::value::Value;
use ferlium::{Compiler, Path, eval::eval_function};
use test_log::test;

use indoc::indoc;

use crate::harness::{TestSession, float, int};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

/// A compound assignment whose index operands contain assignments must report a diagnostic rather
/// than panicking in the borrow checker.
///
/// Found by `grammar_optimization_differential`; all three reproducers reduce to the same defect.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn compound_assignment_through_assigning_index_does_not_panic() {
    for source in [
        "map[a = a = a] += a = a = 0",
        "map[match a = a {a => a}] += a = a = 0",
        "match map[a = a] += a = 0 {a => a = 0}",
    ] {
        let mut session = TestSession::new();
        // Compiling must fail with a diagnostic — `map` and `a` are undefined — and must not panic.
        assert!(
            session.try_compile(source).is_err(),
            "`{source}` must be rejected"
        );
    }
}

/// A mutable argument that is not a place at all must be diagnosed rather than asserted on: the
/// borrow checker's argument-overlap analysis sees it before the mutability check does.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_non_place_mutable_argument_does_not_panic() {
    let mut session = TestSession::new();
    for argument in ["1", "a + 1", "{ a }", "if true { a } else { a }"] {
        session
            .fail_compilation(&format!(
                "fn g(x: &mut int) {{ x = x + 1 }}\nfn f() {{ let mut a = 1; g({argument}) }}\nf()"
            ))
            .expect_mutability_must_be(MutabilityMustBeWhat::Mutable);
    }
    // The overlap analysis it runs inside must still do its job on real places.
    assert_val_eq!(
        session.run("fn g(x: &mut int) { x = x + 1 }\nfn f() { let mut a = 1; g(a); a }\nf()"),
        int(2)
    );
}

/// The same analysis reaches a subscript index before type checking rejects it, so an index that is
/// not an integer literal is dynamic rather than an integer to read out.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_non_integer_subscript_index_does_not_panic() {
    let mut session = TestSession::new();
    session
        .fail_compilation("fn g(x: &mut int) { x = x + 1 }\nfn f(mut y) { g(y[()]) }\nf([1])")
        .expect_type_mismatch("()", "int");
    // A static index still resolves to one, so overlapping elements are still detected.
    assert_val_eq!(
        session.run(
            "fn g(x: &mut int, y: int) { x = x + y }\n\
             fn f() -> int { let mut a = [1, 2]; g(a[0], a[1]); a[0] }\nf()"
        ),
        int(3)
    );
}

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
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn if_else_after_match_expression() {
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
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn if_else_after_nested_block_expression() {
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
}

// A fully concrete (monomorphic) snippet, so the MIR backend can lower it. Like every snippet run
// through a `TestSession`, it executes on both the HIR and MIR interpreters, which must agree.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn concrete_if_else_runs_on_both_backends() {
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
}

// Value-capturing closures (no hidden dictionary evidence) lower to MIR and run on both backends.
// Each case captures by value and is called, exercising `build_closure`, the per-call environment
// clone (so mutations of the captured outer binding after capture do not leak in), the statelessness
// of repeated calls, and the deep copy of a captured mutable array. Generic / dictionary-carrying
// closures (e.g. `|x| x`, `|x| x + b`) are not lowered to MIR yet and stay in the HIR-only
// `simple::lambda` / `simple::closures` tests.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn value_capturing_closures_run_on_both_backends() {
    let mut session = TestSession::new();
    // Basic capture by value.
    assert_val_eq!(session.run("let a = 3.3; let f = || a; f()"), float(3.3));
    assert_val_eq!(session.run("let a = 3; let f = || a; f()"), int(3));
    // The captured environment is a snapshot: mutating the outer binding after capture is invisible.
    assert_val_eq!(
        session.run("let mut a = 1; let f = || a; a = 2; f()"),
        int(1)
    );
    // A closure is stateless across calls: each call sees a fresh copy of the captured environment.
    assert_val_eq!(
        session.run("let mut a = 1; let f = || { a = 2; a }; f(); a"),
        int(1)
    );
    assert_val_eq!(
        session.run("let mut a = 1; let f = || { a = a + 1; a }; f() + f()"),
        int(4)
    );
    // A captured mutable array is deep-copied into the environment.
    assert_val_eq!(
        session.run("let mut a = [1]; let f = || a[0]; a[0] = 2; f()"),
        int(1)
    );
}

// Record field access on a *generic* (row-polymorphic) record lowers to MIR and runs on both
// backends. The field offset is a hidden field-index dictionary parameter, so `v.x` is a `ProjectAt`
// projecting the base place at a run-time index (loaded from that parameter) — never a materialized
// temporary, so the generic field type needs no `Value` layout witness. These exercise: the field
// index as a dictionary-method argument (`v.x + v.y`); a statically-sized field read in value
// position (`v.x + 1`); a generic field cloned through its `Value` dictionary (`v.x` alone); the
// field offset shifting with leading fields (`{name, x, …, y, …}`); and forwarding a field-index
// parameter into a callee (`b` calls `a`, a `LoadFieldIndex` argument). Generic functions made
// first-class (e.g. `(s,).0`) still carry closure dictionary captures and stay HIR-only in
// `simple::records`.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn record_field_access_runs_on_both_backends() {
    let mut session = TestSession::new();
    // A generic field passed as a dictionary-method (`+`) argument, by place.
    assert_val_eq!(session.run("fn s(v) { v.x + v.y } s({x:1, y:2})"), int(3));
    // A generic field cloned through its `Value` dictionary (`v.x` returned alone).
    assert_val_eq!(session.run("fn s(v) { v.x } s({x:1})"), int(1));
    // A statically-sized field read in value position (`v.x` is an `int` here).
    assert_val_eq!(session.run("fn s(v) { v.x + 1 } s({x:1})"), int(2));
    // The field offset shifts past leading and interleaved fields.
    assert_val_eq!(
        session.run("fn s(v) { v.x + v.y } s({name: \"toto\", x:1, z: true, y:2, noise: (1,2)})"),
        int(3)
    );
    // Field access nested through another generic call (`sq` applied to projected fields).
    assert_val_eq!(
        session.run("fn sq(x) { x * x } fn l2(v) { sq(v.x) + sq(v.y) } l2({x:1, y:2})"),
        int(5)
    );
    // Forwarding a field-index parameter into a callee: `b`'s call to `a` passes a `LoadFieldIndex`.
    assert_val_eq!(
        session.run("fn a(x) { x.a } fn b(x) { a(x) } b({a:3})"),
        int(3)
    );
    // A let-bound generic lambda monomorphized at its single call site (static `Project`).
    assert_val_eq!(session.run("let f = |x| x.a; f({a:1})"), int(1));
}

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
    let (value, ty) = {
        let compiler_session = session.session();
        let module = compiler_session.expect_fresh_module(module_and_expr.module_id);
        let ty = module
            .get_function_by_id(expr)
            .unwrap()
            .definition
            .ty_scheme
            .ty
            .ret;
        let value = eval_function(module_and_expr.module_id, expr, vec![], compiler_session)
            .unwrap()
            .into_value();
        (value, ty)
    };
    assert_eq!(
        session.value_to_string(module_and_expr.module_id, value, ty),
        "[{ a: 1 }, { a: 2 }]"
    );

    let module_and_expr = session.compile("[[1, 2], [3, 4]]");
    let expr = module_and_expr
        .expr
        .expect("expected an expression for the formatting regression");
    let (value, ty) = {
        let compiler_session = session.session();
        let module = compiler_session.expect_fresh_module(module_and_expr.module_id);
        let ty = module
            .get_function_by_id(expr)
            .unwrap()
            .definition
            .ty_scheme
            .ty
            .ret;
        let value = eval_function(module_and_expr.module_id, expr, vec![], compiler_session)
            .unwrap()
            .into_value();
        (value, ty)
    };
    assert_eq!(
        session.value_to_string(module_and_expr.module_id, value, ty),
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

// A trait method used as a first-class value is read out of a dictionary method slot, which holds a
// code identity and never a closure. Copying one into a caller's storage is therefore a
// representation copy, even though its function type — which says nothing about a captured
// environment — is not `TrivialCopy`. Passing `len` as a callback is the ordinary way to reach this.
//
// Found by `grammar_optimization_differential`.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_trait_method_passed_as_a_value_is_copied_from_its_dictionary_slot() {
    let mut session = TestSession::new();
    // The callee is unknown in `apply`, so `len` reaches lowering with its evidence unresolved.
    assert_val_eq!(
        session.run("fn apply(g) { g(len) } apply(|k| k([1, 2]))"),
        int(2)
    );
    // The same slot read, instantiated at a different `SizedSeq` impl.
    assert_val_eq!(
        session.run("fn apply(g) { g(len) } apply(|k| k(\"abc\"))"),
        int(3)
    );
    // A generic function value that carries no dictionary is unaffected.
    assert_val_eq!(
        session.run("fn id(x) { x } fn apply(g) { g(id) } apply(|k| k(4))"),
        int(4)
    );
}

// A local needs its `Value` witness for two independent reasons, and allocation is one of them: a
// local owning storage whose size is not statically known takes the dictionary as the `alloca`
// operand supplying that size, whether or not it also needs the ownership methods. Here the local
// constructs a variant in place — nothing to clone or drop — at a type the signature never mentions.
//
// Found by `grammar_optimization_differential`.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_generic_local_that_owns_storage_demands_its_layout_witness() {
    let mut session = TestSession::new();
    session.compile("pub fn f<T>() { let a: T = a; }");
    session.compile("fn f<T>(mut y) { let a: T = a; let b = a; }");
    // The witness is still demanded when the ownership methods are needed as well.
    session.compile("pub fn f<T>() { let a: T = 1; }");
}

// A `break` whose value itself diverges (e.g. `break return x`) terminates the current block while
// lowering that value. The `break` handler must then skip its own unwind / `stack_restore` / jump
// to the loop exit, otherwise the MIR emitter panics with "insertion after terminator".
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
        session.run(
            "fn run() -> int { let c = false; loop { break if c { return 1 } else { 2 } } } run()"
        ),
        int(2)
    );
    assert_val_eq!(
        session.run(
            "fn run() -> int { let c = true; loop { break if c { return 1 } else { 2 } } } run()"
        ),
        int(1)
    );
}

// An `end_project` carries no fallibility of its own: it inherits it from the projection it closes.
// When substituting a generic body at concrete types makes that projection infallible, both halves
// must leave the `invoke` form together — demoting only the projection leaves a body whose
// `end_project` form and fallibility disagree. Indexing an array reached through a struct field is
// the ordinary way to reach this, as the accessor is a projection with an open effect.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_projection_and_its_end_project_leave_the_invoke_form_together() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! { r#"
            struct M { data: [int] }
            fn get(m, i) { m.data[i] }
            get(M { data: [1, 2] }, 1)
        "# }),
        int(2)
    );
    // The projection stays fallible when the index is not known, so the `invoke` form stays too.
    assert_val_eq!(
        session.run(indoc! { r#"
            struct M { cols: int, data: [int] }
            fn get(m, r, c) { m.data[r * m.cols + c] }
            fn run(i) { get(M { cols: 2, data: [1, 2, 3, 4] }, i, 1) }
            run(1)
        "# }),
        int(4)
    );
}
