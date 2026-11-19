// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use test_log::test;

use indoc::{formatdoc, indoc};
use ustr::ustr;

use crate::harness::{RunMode, TestSession, expected_array_infer, expected_tuple, int};
use ferlium::{
    compiler::error::{CompilationErrorImpl, RuntimeErrorKind, SourceFailureKind, UnsafeFeature},
    module::{LocalImplId, id::Id},
    std::core_traits_names::DESERIALIZE_TRAIT_NAME,
    types::effects::*,
};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

pub fn test_mod(session: &mut TestSession, src: &str, f: &str, exp_eff: EffType) {
    let module = session.compile_and_get_module(src);
    let effects = module
        .get_function(ustr(f))
        .unwrap()
        .definition
        .ty_scheme
        .ty()
        .effects
        .clone();
    assert_eq!(effects, exp_eff, "effect mismatch for function {f}");
}

fn test_expr(session: &mut TestSession, src: &str, exp_eff: EffType) {
    let module_and_expr = session.compile(src);
    let module_id = module_and_expr.module_id;
    let expr = module_and_expr.expr.unwrap();
    let module = session.session().expect_fresh_module(module_id);
    let effects = module
        .get_function_by_id(expr)
        .unwrap()
        .definition
        .ty_scheme
        .ty
        .effects
        .clone();
    assert_eq!(effects, exp_eff);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_in_mod() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    let mod_src = "fn r() { effects::read() } fn w() { effects::write() }";
    test_mod(&mut session, mod_src, "r", effect(Read));
    test_mod(&mut session, mod_src, "w", effect(Write));
    let mod_src = "fn rw() { effects::write(); effects::read() }";
    test_mod(&mut session, mod_src, "rw", effects(&[Read, Write]));
    let mod_src = "fn rw() { effects::write(); effects::read() } fn o() { rw() } ";
    test_mod(&mut session, mod_src, "o", effects(&[Read, Write]));
    let mod_src = "fn r() { effects::read() } fn t1() { r() } fn t2() { t1() }";
    test_mod(&mut session, mod_src, "t2", effect(Read));
    let mod_src = "fn rw() { effects::write(); effects::read() } fn o() { ((rw, ).0)() } ";
    test_mod(&mut session, mod_src, "o", effects(&[Read, Write]));
    let mod_src = "fn exits_loop() { loop { break } }";
    test_mod(&mut session, mod_src, "exits_loop", no_effects());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_in_expr() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    test_expr(
        &mut session,
        "let a = |f| f(); a(|| effects::write())",
        effect(Write),
    );
    test_expr(&mut session, "loop { break effects::read() }", effect(Read));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn fn_variance() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    // passing pure to read
    let mod_src = "fn pure() { () } fn f() { effects::take_read(pure) } ";
    test_mod(&mut session, mod_src, "f", effect(Read));

    // passing read to read
    let mod_src = "fn f() { effects::take_read(effects::read) } ";
    test_mod(&mut session, mod_src, "f", effect(Read));
    let mod_src = "fn r() { effects::read() } fn f() { effects::take_read(r) } ";
    test_mod(&mut session, mod_src, "f", effect(Read));

    // passing write to read, should fail
    session
        .fail_compilation("fn f() { effects::take_read(effects::write) }")
        .expect_invalid_effect_inclusion(effect(Write), effect(Read));
    session
        .fail_compilation("fn w() { effects::write() } fn f() { effects::take_read(w) }")
        .expect_invalid_effect_inclusion(effect(Write), effect(Read));

    // passing read, write to read, should fail
    session
        .fail_compilation("fn f() { effects::take_read(effects::read_write) }")
        .expect_invalid_effect_inclusion(effects(&[Read, Write]), effect(Read));
    session
        .fail_compilation(
            "fn rw() { effects::read(); effects::write() } fn f() { effects::take_read(rw) }",
        )
        .expect_invalid_effect_inclusion(effects(&[Read, Write]), effect(Read));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_from_fn_value() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    let mod_src = "fn a(f) { f() } fn b() { a(|| effects::write()) }";
    test_mod(&mut session, mod_src, "a", effect_var(0));
    test_mod(&mut session, mod_src, "b", effect(Write));

    let mod_src = "fn a(f, g) { b(f); f(); g(); () } fn b(f) { a(f, || effects::write()) }";
    test_mod(
        &mut session,
        mod_src,
        "a",
        effect(Write).union(&effect_var(0)),
    );
    test_mod(
        &mut session,
        mod_src,
        "b",
        effect(Write).union(&effect_var(0)),
    );

    let mod_src = "fn b(f) { a(f, || effects::write()) } fn a(f, g) { b(f); f(); g(); () } ";
    test_mod(
        &mut session,
        mod_src,
        "a",
        effect(Write).union(&effect_var(0)),
    );
    test_mod(
        &mut session,
        mod_src,
        "b",
        effect(Write).union(&effect_var(0)),
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn branch_returning_composed_closures_unifies_multiple_effect_variables() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    let mod_src = indoc! {r#"
        fn choose(flag, f, g, h, k) {
            if flag {
                |x| g(f(x))
            } else {
                |x| k(h(x))
            }
        }

        fn call_read_write() {
            let composed = choose(
                true,
                |x| { effects::read(); x },
                |x| x,
                |x| x,
                |x| { effects::write(); x },
            );
            composed(1)
        }
    "#};
    test_mod(
        &mut session,
        mod_src,
        "call_read_write",
        effects(&[Read, Write]),
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_in_recursive_fns() {
    let mut session = TestSession::new();
    let mod_src = "fn a(f) { b(f); f() } fn b(f) { a(f) }";
    test_mod(&mut session, mod_src, "b", effect_var(0));

    let mod_src = "fn a(f, g) { b(f, g); f() } fn b(f, g) { a(f, g); g() }";
    test_mod(&mut session, mod_src, "a", effect_var(0));

    let mod_src = "fn apply(f) { f() } fn rf() { apply(rf) }";
    test_mod(&mut session, mod_src, "rf", no_effects());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_of_fn_called_multiple_times() {
    let mut session = TestSession::new();

    let mod_src = "fn a(f) { f(); f(); f(); () }";
    test_mod(&mut session, mod_src, "a", effect_var(0));
    let mod_src = "fn a(f, g) { f(); g(); g(); f(); f(); g(); () }";
    test_mod(&mut session, mod_src, "a", effect_var(0));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_in_fn_type_ascription() {
    let mut session = TestSession::new();
    use PrimitiveEffect::*;

    let mod_src = "fn g(f: (() -> (), () -> ())) { (f.0(), f.1()) }";
    test_mod(&mut session, mod_src, "g", effect_var(0));
    let mod_src = "fn g(f: ((() -> () ! ()), (() -> () ! read))) { (f.0(), f.1()) }";
    test_mod(&mut session, mod_src, "g", effect(Read));
    let mod_src = "fn g(f: ((() -> () ! fallible), (() -> () ! (read, write)))) { (f.0(), f.1()) }";
    test_mod(
        &mut session,
        mod_src,
        "g",
        effects(&[Fallible, Read, Write]),
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn read_only_callable_coercions_preserve_argument_variance() {
    for reader in [
        "read",
        "black_box(read)",
        "|f| read(f) + captured",
        "readers[0]",
    ] {
        let source = format!(
            "fn read(f: () -> int ! fallible) -> int {{ f() }}
             fn widened_read() -> (&mut (() -> int ! ())) -> int {{ read }}
             fn invoke(f: (&mut (() -> int ! ())) -> int,
                       callback: &mut (() -> int ! ())) -> int {{ f(callback) }}
             let captured = black_box(0);
             let readers = [black_box(widened_read())];
             let mut callback = || 42;
             invoke({reader}, callback)"
        );
        assert_val_eq!(TestSession::new().run(&source), int(42));
    }
    for reader in ["effects::take_read", "black_box(effects::take_read)"] {
        let source = format!(
            "fn invoke(f: (&mut (() -> () ! ())) -> (),
                       callback: &mut (() -> () ! ())) {{ f(callback) }}
             let mut callback = || ();
             invoke({reader}, callback);
             42"
        );
        assert_val_eq!(TestSession::new().run(&source), int(42));
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn read_only_callable_coercions_preserve_heap_arguments() {
    for reader in ["first", "black_box(first)"] {
        let source = format!(
            "fn first(values: [int]) -> int {{ values[0] }}
             fn invoke(reader: (&mut [int]) -> int, values: &mut [int]) -> int {{ reader(values) }}
             let mut values = [7, 8];
             let snapshot = values;
             let observed = invoke({reader}, values);
             values[0] = 9;
             (observed, values, snapshot)"
        );
        assert_val_eq!(
            TestSession::new().run(&source),
            expected_tuple([
                int(7),
                expected_array_infer([int(9), int(8)]),
                expected_array_infer([int(7), int(8)]),
            ])
        );
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn writing_callable_coercions_preserve_argument_invariance() {
    let source = "fn replace(f: &mut (() -> int ! fallible)) { f = || [1][1]; }
                  fn invoke(f: (&mut (() -> int ! ())) -> (),
                            callback: &mut (() -> int ! ())) { f(callback) }
                  let mut callback = || 42;
                  invoke(replace, callback)";
    TestSession::new()
        .fail_compilation(source)
        .expect_invalid_effect_inclusion(effect(PrimitiveEffect::Fallible), no_effects());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_access_must_be_fallible() {
    use PrimitiveEffect::*;
    let mut session = TestSession::new();

    let mod_src = "fn f(a: [_]) { a[0] } ";
    test_mod(&mut session, mod_src, "f", effect(Fallible));
    let mod_src = "fn f() { let mut a = []; a[0] = 1; } ";
    test_mod(&mut session, mod_src, "f", effect(Fallible));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_unsafe_is_rejected_in_user_code() {
    let mut session = TestSession::new();

    match session
        .fail_compilation("effects_unsafe { [1][0] }")
        .into_inner()
    {
        CompilationErrorImpl::UnsafeFeatureUseNotAllowed { feature, .. } => {
            assert_eq!(feature, UnsafeFeature::EffectsUnsafe);
        }
        other => panic!("expected UnsafeFeatureUseNotAllowed error, got {other:?}"),
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_unsafe_erases_effects_in_trusted_code() {
    let mut session = TestSession::new();
    session.allow_unsafe();
    test_expr(&mut session, "effects_unsafe { 1 / 0 }", EffType::empty());
    test_mod(
        &mut session,
        "fn f(x: int) { effects_unsafe { idiv(1, x) } }",
        "f",
        EffType::empty(),
    );
}

/// A source failure within `effects_unsafe` poisons execution rather than reaching a caller that
/// does not expect it.
fn assert_effect_violation_by_division_by_zero(session: &mut TestSession, src: &str) {
    let error = session.try_run(src).expect_err("the division fails");
    assert_eq!(error.kind(), RuntimeErrorKind::EffectViolation);
    assert_eq!(
        error.effect_violation().unwrap().kind(),
        SourceFailureKind::DivisionByZero
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_unsafe_failure_in_infallible_function_poisons() {
    let mut session = TestSession::new();
    session.allow_unsafe();
    assert_effect_violation_by_division_by_zero(
        &mut session,
        "fn f(x: int) -> int { effects_unsafe { idiv(1, x) } }\nf(0)",
    );
    // Poisoning ends that execution only: the session runs again.
    assert_val_eq!(session.run("1 + 1"), int(2));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_unsafe_failure_in_specialized_infallible_function_poisons() {
    // `apply`'s effects are its callback's; with a pure one, its specialization cannot fail.
    let mut session = TestSession::new();
    session.allow_unsafe();
    assert_effect_violation_by_division_by_zero(
        &mut session,
        "fn apply(f, x) { effects_unsafe { idiv(1, f(x)) } }\napply(|x| x, 0)",
    );
}

const PROBE: &str = indoc! { r#"
    struct Probe(int)

    impl Value for Probe {
        fn eq(left: Probe, right: Probe) -> bool { left.0 == right.0 }
        fn to_string(value: Probe) -> string { to_string(value.0) }
        fn hash(value: Probe, state: &mut hasher) { hash(value.0, state) }
        fn clone(source: Probe) -> Probe { Probe(source.0) }
        fn drop(target: &mut Probe) { testing::record_tracked_drop(target.0) }
    }
"# };

/// Runs `src`, which defines `Probe` and resets the tracked drops, under each mode on its own,
/// expecting an effect violation by a division by zero after which `drops` are logged.
fn assert_effect_violation_dropping(src: &str, drops: isize) {
    for mode in RunMode::ALL {
        let mut session = TestSession::new();
        session.allow_unsafe();
        session.run_modes([mode]);
        let error = session.try_run(src).expect_err("the division fails");
        assert_eq!(error.kind(), RuntimeErrorKind::EffectViolation, "{mode:?}");
        assert_eq!(
            error.effect_violation().unwrap().kind(),
            SourceFailureKind::DivisionByZero,
            "{mode:?}"
        );
        assert_val_eq!(
            session.run("testing::tracked_drop_log()"),
            int(drops),
            "{mode:?}"
        );
    }
}

/// A failure within `effects_unsafe` is an effect violation where it is raised, even in a function
/// that may fail, and no cleanup runs for it, neither in the block nor around it.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_unsafe_failure_in_fallible_function_poisons_without_cleanup() {
    assert_effect_violation_dropping(
        &formatdoc! { r#"
            {PROBE}
            fn f(x: int) -> int {{
                let outer = Probe(1);
                let a = idiv(1, x);
                effects_unsafe {{
                    let inner = Probe(2);
                    idiv(1, a - 1)
                }}
            }}

            testing::reset_tracked_drops();
            f(1)
        "# },
        0,
    );
}

/// A function called within `effects_unsafe` fails as usual, running its own cleanup; the failure
/// becomes an effect violation once it reaches the block.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_unsafe_failure_of_a_callee_poisons_after_its_cleanup() {
    assert_effect_violation_dropping(
        &formatdoc! { r#"
            {PROBE}
            fn inner(x: int) -> int {{
                let local = Probe(3);
                idiv(1, x)
            }}

            fn f(x: int) -> int {{
                let outer = Probe(1);
                effects_unsafe {{ inner(x) }}
            }}

            testing::reset_tracked_drops();
            f(0)
        "# },
        3,
    );
}

/// A function generic in its effects but called at a pure instantiation, by name or through a
/// value, cannot fail at that call: a failure within its `effects_unsafe` is an effect violation,
/// and the caller's cleanup does not run.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_unsafe_failure_in_pure_instantiation_of_effect_generic_function_poisons() {
    for call in [
        "g(|z| z, 0)",
        "{ let h: ((int) -> int, int) -> int = g; h(|z| z, 0) }",
    ] {
        assert_effect_violation_dropping(
            &formatdoc! { r#"
                {PROBE}
                fn g<! E>(f: (int) -> int ! E, x: int) -> int {{
                    let y = f(x);
                    effects_unsafe {{ idiv(1, y) }}
                }}

                fn main(x: int) -> int {{
                    let p = Probe(1);
                    let a = idiv(1, x + 1);
                    {call} + a
                }}

                testing::reset_tracked_drops();
                main(0)
            "# },
            0,
        );
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_output_effects_resolve_to_impl_effects() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    // The TestEff impl for int is pure, the one for bool has the read effect.
    let mod_src = indoc! {r#"
        fn pure_project(x: int) -> int { testing::TestEff::eff_project(x) }
        fn effectful_project(x: bool) -> int { testing::TestEff::eff_project(x) }
    "#};
    test_mod(&mut session, mod_src, "pure_project", EffType::empty());
    test_mod(&mut session, mod_src, "effectful_project", effect(Read));

    // The same resolution happens for expressions.
    test_expr(
        &mut session,
        "testing::TestEff::eff_project(1)",
        EffType::empty(),
    );
    test_expr(
        &mut session,
        "testing::TestEff::eff_project(true)",
        effect(Read),
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_output_effects_are_quantified_in_generic_functions() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    // The generic function's effect is the trait's output effect variable,
    // which gets resolved at concrete call sites through the trait constraint.
    let mod_src = indoc! {r#"
        fn generic_project(x) { testing::TestEff::eff_project(x) }
        fn call_pure(y: int) -> int { generic_project(y) }
        fn call_effectful(y: bool) -> int { generic_project(y) }
    "#};
    test_mod(&mut session, mod_src, "generic_project", effect_var(0));
    test_mod(&mut session, mod_src, "call_pure", EffType::empty());
    test_mod(&mut session, mod_src, "call_effectful", effect(Read));

    // The generic function's scheme carries the effect variable in the
    // trait constraint's output effects.
    let module = session.compile_and_get_module(mod_src);
    let def = &module
        .get_function(ustr("generic_project"))
        .unwrap()
        .definition;
    let output_effs = def
        .ty_scheme
        .constraints
        .iter()
        .find_map(|constraint| {
            let (_, _, _, _, output_effs, _) = constraint.as_have_trait()?;
            (!output_effs.is_empty()).then(|| output_effs.clone())
        })
        .expect("expected a trait constraint with output effects");
    assert_eq!(output_effs, vec![effect_var(0)]);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_output_effects_propagate_through_blanket_impls() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    // The blanket TestEff impl over Option<T> forwards the effect of T's impl.
    let mod_src = indoc! {r#"
        fn pure_project() -> int { testing::TestEff::eff_project(testing::some_int(1)) }
        fn effectful_project() -> int { testing::TestEff::eff_project(testing::some_bool(true)) }
    "#};
    test_mod(&mut session, mod_src, "pure_project", EffType::empty());
    test_mod(&mut session, mod_src, "effectful_project", effect(Read));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn associated_effect_bindings_accept_parenthesized_values() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    let mod_src = indoc! {r#"
        trait Do<Self |-> ! Eff> {
            fn do(value: Self) ! Eff;
        }

        struct Pure;
        struct Single;
        struct Trailing;
        struct Union;

        impl Do for <Self = Pure |-> ! Eff = ()> {
            fn do(value: Pure) {}
        }
        impl Do for <Self = Single |-> ! Eff = (read)> {
            fn do(value: Single) { effects::read() }
        }
        impl Do for <Self = Trailing |-> ! Eff = (read,)> {
            fn do(value: Trailing) { effects::read() }
        }
        impl Do for <Self = Union |-> ! Eff = (read, write)> {
            fn do(value: Union) { effects::read(); effects::write() }
        }

        fn call_pure() { do(Pure) }
        fn call_single() { do(Single) }
        fn call_trailing() { do(Trailing) }
        fn call_union() { do(Union) }
    "#};

    test_mod(&mut session, mod_src, "call_pure", EffType::empty());
    test_mod(&mut session, mod_src, "call_single", effect(Read));
    test_mod(&mut session, mod_src, "call_trailing", effect(Read));
    test_mod(&mut session, mod_src, "call_union", effects(&[Read, Write]));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn concrete_trait_output_effect_does_not_leak_inference_slot() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    let mod_src = indoc! {r#"
        trait Do<Self |-> ! Eff> {
            fn do(value: Self) ! Eff;
        }

        struct ReadOnly;
        impl Do for <Self = ReadOnly |-> ! Eff = read> {
            fn do(value: ReadOnly) { effects::read() }
        }

        fn call_read() { do(ReadOnly) }
    "#};

    test_mod(&mut session, mod_src, "call_read", effect(Read));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_output_effects_dispatch_at_runtime() {
    let mut session = TestSession::new();

    // Trait output effects are compile-time only and do not change dispatch.
    assert_val_eq!(session.run("testing::TestEff::eff_project(21)"), int(42));
    assert_val_eq!(session.run("testing::TestEff::eff_project(true)"), int(1));
    assert_val_eq!(session.run("testing::TestEff::eff_project(false)"), int(0));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_output_effects_are_rejected_in_restricted_contexts() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    // The TestEff impl for string has the write effect, so a callback using it
    // cannot be passed where only the read effect is allowed.
    session
        .fail_compilation(
            r#"fn f() { effects::take_read(|| { testing::TestEff::eff_project("s"); () }) }"#,
        )
        .expect_invalid_effect_inclusion(effect(Write), effect(Read));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_output_effects_multiple_slots_resolve_independently() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    // The TestEffPair impl for bool has read in its first effect slot and
    // write in its second one; each method must resolve to its own slot.
    let mod_src = indoc! {r#"
        fn first(x: bool) -> int { testing::TestEffPair::eff_pair_first(x) }
        fn second(x: bool) -> int { testing::TestEffPair::eff_pair_second(x) }
        fn both(x: bool) -> int { testing::TestEffPair::eff_pair_first(x) + testing::TestEffPair::eff_pair_second(x) }
    "#};
    test_mod(&mut session, mod_src, "first", effect(Read));
    test_mod(&mut session, mod_src, "second", effect(Write));
    test_mod(&mut session, mod_src, "both", effects(&[Read, Write]));

    // The same holds through generic functions; a function using both slots
    // publishes one effect variable for both, which callers still resolve.
    let generic_src = indoc! {r#"
        fn generic_first(x) { testing::TestEffPair::eff_pair_first(x) }
        fn generic_second(x) { testing::TestEffPair::eff_pair_second(x) }
        fn generic_both(x) { testing::TestEffPair::eff_pair_first(x) + testing::TestEffPair::eff_pair_second(x) }
        fn call_first(y: bool) -> int { generic_first(y) }
        fn call_second(y: bool) -> int { generic_second(y) }
        fn call_both(y: bool) -> int { generic_both(y) }
    "#};
    test_mod(&mut session, generic_src, "generic_first", effect_var(0));
    test_mod(&mut session, generic_src, "generic_second", effect_var(0));
    test_mod(&mut session, generic_src, "generic_both", effect_var(0));
    test_mod(&mut session, generic_src, "call_first", effect(Read));
    test_mod(&mut session, generic_src, "call_second", effect(Write));
    test_mod(
        &mut session,
        generic_src,
        "call_both",
        effects(&[Read, Write]),
    );

    // Effects are compile-time only; both methods dispatch normally.
    assert_val_eq!(
        session.run("testing::TestEffPair::eff_pair_first(true)"),
        int(1)
    );
    assert_val_eq!(
        session.run("testing::TestEffPair::eff_pair_second(true)"),
        int(2)
    );

    // A read-only context accepts the first (read) slot but rejects the
    // second (write) one.
    session.compile(
        r#"fn ok() { effects::take_read(|| { testing::TestEffPair::eff_pair_first(true); () }) }"#,
    );
    session
        .fail_compilation(
            r#"fn bad() { effects::take_read(|| { testing::TestEffPair::eff_pair_second(true); () }) }"#,
        )
        .expect_invalid_effect_inclusion(effect(Write), effect(Read));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_output_effects_can_join_multiple_effect_variables() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    let concrete_src = indoc! {r#"
        fn pure_join() -> int { let x: int = 1; let y: int = 2; testing::TestEffJoin::eff_join(testing::EffPair(x, y)) }
        fn read_join() -> int { let x: int = 1; testing::TestEffJoin::eff_join(testing::EffPair(x, true)) }
        fn write_join() -> int { let x: int = 1; testing::TestEffJoin::eff_join(testing::EffPair(x, "s")) }
        fn read_write_join() -> int { testing::TestEffJoin::eff_join(testing::EffPair(true, "s")) }
    "#};
    test_mod(&mut session, concrete_src, "pure_join", EffType::empty());
    test_mod(&mut session, concrete_src, "read_join", effect(Read));
    test_mod(&mut session, concrete_src, "write_join", effect(Write));
    test_mod(
        &mut session,
        concrete_src,
        "read_write_join",
        effects(&[Read, Write]),
    );

    let generic_src = indoc! {r#"
        fn generic_join(a, b) { testing::TestEffJoin::eff_join(testing::EffPair(a, b)) }
        fn call_pure() -> int { let x: int = 1; let y: int = 2; generic_join(x, y) }
        fn call_read() -> int { let x: int = 1; generic_join(x, true) }
        fn call_write() -> int { let x: int = 1; generic_join(x, "s") }
        fn call_read_write() -> int { generic_join(true, "s") }
    "#};
    test_mod(&mut session, generic_src, "generic_join", effect_var(0));
    test_mod(&mut session, generic_src, "call_pure", EffType::empty());
    test_mod(&mut session, generic_src, "call_read", effect(Read));
    test_mod(&mut session, generic_src, "call_write", effect(Write));
    test_mod(
        &mut session,
        generic_src,
        "call_read_write",
        effects(&[Read, Write]),
    );
}

/// An adaptor whose impl leaves its output effect unwritten performs the effect of the iterator
/// it wraps, as `NextEffect = E` with `I: Iterator<Item = int ! NextEffect = E>` would say, also
/// when its `where` clause only implies that requirement. So does a function, recursive or not,
/// whose `where` clause implies it. When the implied requirement is on a concrete type, the
/// selected implementation gives its effect.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn an_adaptor_performs_the_effect_of_the_iterator_it_wraps() {
    use PrimitiveEffect::*;

    let src = indoc! {r#"
        struct Div { n: int }

        impl Iterator for Div {
            fn next(it: &mut Div) -> Option<int> {
                it.n = it.n - 1;
                Some(idiv(1, it.n))
            }
        }

        struct Wrap<I> { inner: I }

        impl<I> Iterator for Wrap<I> where I: Iterator<Item = int> {
            fn next(it: &mut Wrap<I>) -> Option<int> {
                next(it.inner)
            }
        }

        trait Tagged<Self> where Self: Iterator<Item = int> {}

        impl Tagged for Div {}

        struct TaggedWrap<I> { inner: I }

        impl<I> Iterator for TaggedWrap<I> where I: Tagged {
            fn next(it: &mut TaggedWrap<I>) -> Option<int> {
                next(it.inner)
            }
        }

        fn wrapped_div() -> Option<int> {
            let mut wrapped = Wrap { inner: Div { n: 1 } };
            next(wrapped)
        }

        fn wrapped_array() -> Option<int> {
            let mut wrapped = Wrap { inner: iter([1]) };
            next(wrapped)
        }

        fn tagged_wrapped_div() -> Option<int> {
            let mut wrapped = TaggedWrap { inner: Div { n: 1 } };
            next(wrapped)
        }

        struct DivWrap { inner: Div }

        impl Iterator for DivWrap where Div: Tagged {
            fn next(it: &mut DivWrap) -> Option<int> {
                next(it.inner)
            }
        }

        fn div_wrapped() -> Option<int> {
            let mut wrapped = DivWrap { inner: Div { n: 1 } };
            next(wrapped)
        }

        fn pull_div() -> Option<int> where Div: Tagged {
            let mut div = Div { n: 1 };
            next(div)
        }

        fn pull<I>(it: &mut I) -> Option<int> where I: Tagged {
            next(it)
        }

        fn pull_after<I>(it: &mut I, n: int) -> Option<int> where I: Tagged {
            if n > 0 {
                pull_after(it, n - 1)
            } else {
                next(it)
            }
        }

        fn pulled_div() -> Option<int> {
            let mut div = Div { n: 1 };
            pull(div)
        }

        fn pulled_after_div() -> Option<int> {
            let mut div = Div { n: 1 };
            pull_after(div, 2)
        }
    "#};
    let mut session = TestSession::new();
    test_mod(&mut session, src, "wrapped_div", effect(Fallible));
    test_mod(&mut session, src, "wrapped_array", EffType::empty());
    test_mod(&mut session, src, "tagged_wrapped_div", effect(Fallible));
    test_mod(&mut session, src, "pulled_div", effect(Fallible));
    test_mod(&mut session, src, "pulled_after_div", effect(Fallible));
    test_mod(&mut session, src, "div_wrapped", effect(Fallible));
    test_mod(&mut session, src, "pull_div", effect(Fallible));
    // A source failure, not one escaping a call whose type says it cannot fail.
    for call in [
        "wrapped_div()",
        "tagged_wrapped_div()",
        "pulled_div()",
        "pulled_after_div()",
        "div_wrapped()",
        "pull_div()",
    ] {
        assert_eq!(
            session.fail_run(&format!("{src}\n{call}")),
            SourceFailureKind::DivisionByZero,
            "{call}"
        );
    }
}

/// A call that a parent held by the dictionary of a written requirement answers performs the
/// effect of that dictionary, as the caller gives it, even where the types of the parent are
/// known: here `Seq` holds its iterator's `Iterator`, whose effect `Div` fixes to `fallible`,
/// whether the clause writes `Div` or inference finds it, even after the call.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_held_parent_of_known_types_performs_the_effect_of_the_callers_dictionary() {
    use PrimitiveEffect::*;

    let src = indoc! {r#"
        struct Div { n: int }

        impl Iterator for Div {
            fn next(it: &mut Div) -> Option<int> {
                it.n = it.n - 1;
                Some(idiv(1, it.n))
            }
        }

        struct Box;

        impl Seq for <Self = Box |-> Item = int, Iter = Div> {
            fn iter(b: Box) -> Div {
                Div { n: 1 }
            }
        }

        trait Make<Self |-> Out> {
            fn make(x: Self) -> Out;
        }

        impl Make for <Self = bool |-> Out = Div> {
            fn make(x: bool) -> Div {
                Div { n: 2 }
            }
        }

        fn same<A>(a: A, b: A) -> A {
            a
        }

        fn walk<S>(s: S) -> Option<int> where S: Seq<Item = _, Iter = ITER> {
            let mut it: Div = iter(s);
            next(it)
        }

        fn walk_late<S>(s: S) -> Option<int> where S: Seq<Item = _, Iter = ITER> {
            let mut it = iter(s);
            let walked = next(it);
            let made = same(it, make(true));
            walked
        }

        fn walked() -> Option<int> {
            walk(Box)
        }

        fn walked_late() -> Option<int> {
            walk_late(Box)
        }
    "#};
    for iter in ["Div", "_"] {
        let src = src.replace("ITER", iter);
        let mut session = TestSession::new();
        for f in ["walked", "walked_late"] {
            test_mod(&mut session, &src, f, effect(Fallible));
            // A source failure, not one escaping a call whose type says it cannot fail.
            assert_eq!(
                session.fail_run(&format!("{src}\n{f}()")),
                SourceFailureKind::DivisionByZero,
                "{f} with `{iter}`"
            );
        }
    }
}

/// An implied requirement that the dictionary of the written one does not hold, as `Container`
/// does not hold its item's `Iterator`, performs the effect of the implementation of its types
/// once they are known, whether the `where` clause writes them or inference finds them, even
/// after the body uses it.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn an_implied_requirement_of_known_types_performs_the_effect_of_their_implementation() {
    use PrimitiveEffect::*;

    let src = indoc! {r#"
        struct Div { n: int }

        impl Iterator for Div {
            fn next(it: &mut Div) -> Option<int> {
                it.n = it.n - 1;
                Some(idiv(1, it.n))
            }
        }

        struct Source;

        trait Container<Self |-> Item> where Item: Iterator<Item = int> {
            fn get(value: Self) -> Item;
        }

        impl Container for <Self = Source |-> Item = Div> {
            fn get(value: Source) -> Div {
                Div { n: 1 }
            }
        }

        trait Make<Self |-> Out> {
            fn make(x: Self) -> Out;
        }

        impl Make for <Self = bool |-> Out = Div> {
            fn make(x: bool) -> Div {
                Div { n: 2 }
            }
        }

        fn same<A>(a: A, b: A) -> A {
            a
        }

        struct Wrap<T> { source: T }

        impl<T> Iterator for Wrap<T> where T: Container<Item = ITEM> {
            fn next(it: &mut Wrap<T>) -> Option<int> {
                let mut inner: Div = get(it.source);
                next(inner)
            }
        }

        fn wrapped() -> Option<int> {
            let mut wrapped = Wrap { source: Source };
            next(wrapped)
        }

        fn pull<T>(x: T) -> Option<int> where T: Container<Item = ITEM> {
            let mut inner: Div = get(x);
            next(inner)
        }

        fn pull_late<T>(x: T) -> Option<int> where T: Container<Item = ITEM> {
            let mut inner = get(x);
            let pulled = next(inner);
            let made = same(inner, make(true));
            pulled
        }

        fn pulled() -> Option<int> {
            pull(Source)
        }

        fn pulled_late() -> Option<int> {
            pull_late(Source)
        }
    "#};
    for item in ["Div", "_"] {
        let src = src.replace("ITEM", item);
        let mut session = TestSession::new();
        for f in ["wrapped", "pulled", "pulled_late"] {
            test_mod(&mut session, &src, f, effect(Fallible));
            // A source failure, not one escaping a call whose type says it cannot fail.
            assert_eq!(
                session.fail_run(&format!("{src}\n{f}()")),
                SourceFailureKind::DivisionByZero,
                "{f} with `{item}`"
            );
        }
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_impl_effect_must_not_have_more_than_def_effects() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    // Pure trait method cannot be implemented with a fallible body.
    session
        .fail_compilation(
            r#"
        trait Pure<Self> {
            fn pure(x: Self);
        }

        struct S;

        impl Pure for S {
            fn pure(x: S) {
                panic("not pure")
            }
        }
        "#,
        )
        .expect_trait_method_effect_mismatch("Pure", "pure", &EffType::empty(), &effect(Fallible));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_impl_effect_must_have_at_least_def_effects() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    // Deserialize trait method is fallible, pure implementation is OK (subset).
    let mod_src = indoc! { r#"
	    struct S;
	    impl Deserialize {
	        fn deserialize(v) {
	            S
	        }
	    }
    "# };
    let deserialize_trait = session.std_trait(DESERIALIZE_TRAIT_NAME);
    let module = session.compile_and_get_module(mod_src);
    let deserialize_impl = (0..module.impl_count())
        .map(LocalImplId::from_index)
        .find(|&id| {
            let trait_id = module.get_impl_trait_key_by_id(id).unwrap().trait_id();
            trait_id == deserialize_trait
        })
        .unwrap();
    let fn_id = module.get_impl_data(deserialize_impl).unwrap().methods[0];
    let effects = &module
        .get_function_by_id(fn_id)
        .unwrap()
        .definition
        .ty_scheme
        .ty()
        .effects;
    assert_eq!(effects, &effect(Fallible));
}
