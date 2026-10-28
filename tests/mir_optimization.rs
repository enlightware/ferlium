// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Staging and rewritability checks for the MIR optimization pipeline.
//!
//! Structural properties of optimized MIR, and the staging rules around it.
//!
//! That optimization preserves *behaviour* is checked elsewhere, and far more broadly: the test
//! harness runs every language snippet under `RunMode::OptimizedMir` beside the HIR and MIR
//! interpreters and asserts all three agree, in value and in failure. What belongs here is what
//! that cannot see — the shape of the emitted MIR, and which stage a session reads.
//!
//! Every function reachable from a corpus snippet, including every function of the standard
//! library, is rewritten through `FunctionEdit`, which runs the full MIR verifier on the result in
//! test builds. See `doc/plans/partial-evaluation.md`.

use ferlium::{CompilerSession, MirOptimization};

/// Snippets covering the forms a rewrite must carry through, shared with the crate's budget test.
const CORPUS: &[(&str, &str)] = include!("harness/mir_corpus.rs");

fn session(optimization: MirOptimization) -> CompilerSession {
    let mut session = CompilerSession::new();
    session.set_mir_optimization(optimization);
    session
}

/// Emits the MIR of `src` under `optimization`, in a fresh session.
fn emit(name: &str, src: &str, optimization: MirOptimization) -> String {
    session(optimization).emit_mir(name, src)
}

/// Every corpus snippet optimizes. A panic here means a pass produced a function the verifier
/// rejects, which is the point of running this over the whole corpus and the standard library.
#[test]
fn every_corpus_snippet_optimizes() {
    for (name, src) in CORPUS {
        emit(name, src, MirOptimization::Enabled);
    }
}

/// The folding gate from `doc/plans/partial-evaluation.md`: constant arithmetic collapses into a
/// single store into the return place, with no call left.
#[test]
fn constant_arithmetic_folds_away() {
    let (name, src) = CORPUS[1];
    let optimized = emit(name, src, MirOptimization::Enabled);
    let main = optimized
        .split("fn main")
        .nth(1)
        .expect("the corpus defines main");
    assert_eq!(calls(main), 0, "`let x = 2 + 3; x * 7` must fold:\n{main}");
    assert!(
        main.contains("= 35") && main.contains("ret @c"),
        "the folded result must be returned:\n{main}"
    );
}

/// A non-capturing closure bound to a local is a bare function in a single-store cell: the call
/// through it becomes direct, is inlined, and the body keeps no call-depth check.
#[test]
fn a_local_non_capturing_closure_is_called_directly() {
    let optimized = emit(
        "closure",
        "fn apply(x: int) -> int { let f = |y| y + 1; f(x) }",
        MirOptimization::Enabled,
    );
    let apply = optimized
        .split("fn apply")
        .nth(1)
        .expect("the module defines apply")
        .split("\nfn ")
        .next()
        .expect("apply has a body");
    assert!(
        !apply.contains("lambda") && !apply.contains("check_call_depth"),
        "the closure must be inlined and the check proved unnecessary:\n{apply}"
    );
}

#[test]
fn a_known_callable_stays_direct_after_a_read_only_call() {
    let optimized = emit(
        "callable_place",
        r#"
        #[inline(never)] fn inc(x: int) -> int { x + 1 }
        #[inline(never)] fn observe(f, x: int) -> int { f(x) }
        fn run(x: int) -> int {
            let f = inc;
            observe(f, x) + f(x)
        }
        "#,
        MirOptimization::Enabled,
    );
    let run = rendered_function_with_prefix(&optimized, "run");
    assert!(run.contains("call callable_place::observe("), "{run}");
    assert!(run.contains("call callable_place::inc("), "{run}");
    assert!(
        !run.contains("call %"),
        "the local callback must stay known: {run}"
    );
}

/// An owned string cannot enter the constant pool, but its immutable contents can. Folding a
/// formatter therefore leaves the terminal `StaticStr` -> fresh `string` construction rather than
/// the formatter call itself.
#[test]
fn a_constant_string_result_reifies_constructively() {
    let optimized = emit(
        "constructive_string_reification",
        "fn main() -> string { to_string(42) }",
        MirOptimization::Enabled,
    );
    let main = rendered_function_with_prefix(&optimized, "main");
    assert!(
        !main.contains("Value<std::int>::to_string"),
        "the known formatter call must be evaluated:
{main}"
    );
    assert!(
        main.contains("StaticStr = \"42\"") && main.contains("call std::string_from_static"),
        "the folded string must be reconstructed from immutable text:
{main}"
    );
}

/// Keep the derivator generic: its raw tuple formatter calls `Value<()>::to_string`, while the
/// optimizer knows every unit-typed argument, constructively reifies the result, and fuses the
/// temporary string into the builder's static append.
#[test]
fn a_reified_unit_formatter_fuses_into_a_static_append() {
    let src = "fn show(x) { match x { None => \"no\", Some(x) => f\"{x}\", _ => \"?\" } }\n\
               show(Other)";
    let raw = emit("reified_unit_formatter", src, MirOptimization::Disabled);
    assert!(
        raw.contains("call std::Value<std::()>::to_string"),
        "the test must exercise the generic derivator rather than a unit special case:
{raw}"
    );

    let optimized = emit("reified_unit_formatter", src, MirOptimization::Enabled);
    assert!(
        !optimized.contains("call std::Value<std::()>::to_string"),
        "unit formatting must fold in every generated implementation:
{optimized}"
    );
    let tuple =
        rendered_function_with_prefix(&optimized, "std::Value<(std::(),)>::to_string#impl:");
    assert!(
        tuple.contains("StaticStr = \"()\"")
            && tuple.contains("call no_value std::string_push_static_str")
            && !tuple.contains("call no_value std::string_push_str"),
        "the reified unit string must append without an owned temporary:
{tuple}"
    );
}

/// Compiler-generated `Value` ownership glue must make the same `TrivialCopy` decision as
/// ordinary ownership elaboration. `Some(())` stores its constructor argument as `((),)`, but both
/// that zero-sized tuple and the enclosing tagged union are representation-copyable: cloning the
/// union copies only its tag, and dropping it has no semantic work.
#[test]
fn generated_trivial_value_glue_uses_representation_operations() {
    let raw = emit(
        "trivial_generated_value_glue",
        "fn show(x) { match x { None => \"no\", Some(x) => f\"{x}\", _ => \"?\" } }\n\
         show(Other)",
        MirOptimization::Disabled,
    );

    for ty in ["(std::(),)", "None | Other | Some (std::())"] {
        let clone = rendered_function_with_prefix(&raw, &format!("std::Value<{ty}>::clone#impl:"));
        assert!(
            clone.contains(if ty == "(std::(),)" {
                "memcpy %p0 to %r0"
            } else {
                "memcpy %p0 to %p1"
            }),
            "generated clone for `{ty}` must copy the whole representation:\n{clone}"
        );
        assert_eq!(
            calls(clone),
            0,
            "trivial clone must call no Value method:\n{clone}"
        );
        assert!(
            !clone.contains("extract_tag"),
            "trivial variant clone must not walk its cases:\n{clone}"
        );

        let drop = rendered_function_with_prefix(&raw, &format!("std::Value<{ty}>::drop#impl:"));
        assert_eq!(
            calls(drop),
            0,
            "trivial drop must call no Value method:\n{drop}"
        );
        assert!(
            !drop.contains("extract_tag"),
            "trivial variant drop must not walk its cases:\n{drop}"
        );
    }
}

/// A managed aggregate cannot use the whole-value fast path, but its concrete trivial members
/// still need representation copies and no drops. This prevents unit/int/native clone calls from
/// reappearing whenever one sibling owns a resource.
#[test]
fn generated_mixed_value_glue_skips_trivial_members() {
    let raw = emit(
        "mixed_generated_value_glue",
        "(1, \"a\") == (1, \"b\")",
        MirOptimization::Disabled,
    );
    let clone =
        rendered_function_with_prefix(&raw, "std::Value<(std::int, std::string)>::clone#impl:");
    assert!(clone.contains(
        "%r0: place int = subfield @c0 from %p1\n    %r1: place int = subfield @c0 from %p0\n    memcpy %r1 to %r0"
    ), "the int member must be copied directly:\n{clone}");
    assert!(
        clone.contains("Value<std::string>::clone"),
        "the managed member must retain semantic clone:\n{clone}"
    );
    assert!(
        !clone.contains("Value<std::int>::clone"),
        "the trivial member must not call semantic clone:\n{clone}"
    );

    let drop =
        rendered_function_with_prefix(&raw, "std::Value<(std::int, std::string)>::drop#impl:");
    assert!(
        drop.contains("Value<std::string>::drop"),
        "the managed member must retain semantic drop:\n{drop}"
    );
    assert!(
        !drop.contains("Value<std::int>::drop"),
        "the trivial member must not call semantic drop:\n{drop}"
    );
}

/// Trivial array literals use the compiler-known array constructor. Resource-valued elements keep
/// the generic in-place Buffer path, because constructing them from borrowed operands would need a
/// semantic clone dictionary rather than a representation copy.
#[test]
fn array_literal_lowering_uses_build_array_only_for_trivial_elements() {
    let ints = emit(
        "trivial_array_literal",
        "fn main() -> [int] { [1, 2] }",
        MirOptimization::Disabled,
    );
    let ints = rendered_function(&ints, "main");
    assert!(
        ints.contains("build_array<int>"),
        "an int array should use the explicit MIR constructor:\n{ints}"
    );

    let strings = emit(
        "resource_array_literal",
        "fn main() -> [string] { [\"a\", \"b\"] }",
        MirOptimization::Disabled,
    );
    let strings = rendered_function(&strings, "main");
    assert!(
        !strings.contains("build_array<string>"),
        "a string array must retain in-place element construction:\n{strings}"
    );
    assert!(
        strings.contains("buffer_with_capacity"),
        "the non-trivial fallback must still allocate the canonical array Buffer:\n{strings}"
    );
}

/// Resource-valued reification turns the complete constant pipeline into one fresh array
/// construction. In particular, no compile-time Buffer is put in the constant pool and none of
/// the source/intermediate arrays survives merely to be dropped.
#[test]
fn constant_array_pipeline_reifies_to_one_build_array() {
    let optimized = emit(
        "constant_array_pipeline",
        "fn main() -> [int] { [1, 2] |> concat([3, 4]) |> map(|x| x*x) }",
        MirOptimization::Enabled,
    );
    let main = rendered_function(&optimized, "main");
    assert_eq!(
        main.matches("build_array<int>").count(),
        1,
        "the complete expression should become one runtime construction:\n{main}"
    );
    assert!(
        main.contains("build_array<int> [@c0, @c1, @c2, @c3] to %p0"),
        "the final array should be built directly into the return place:\n{main}"
    );
    for value in ["int = 1", "int = 4", "int = 9", "int = 16"] {
        assert!(
            main.contains(value),
            "missing folded element `{value}`:\n{main}"
        );
    }
    assert_eq!(
        calls(main),
        0,
        "the constant pipeline must contain no calls:\n{main}"
    );
    assert!(
        !main.contains("drop "),
        "superseded arrays must be removed with their cleanup:\n{main}"
    );
}

/// The iterator pipeline retains one concrete closed family of each kind: its implementations'
/// own effect variables take their least solution, so no open helper family is needed, and
/// provisional caller-local effect rows create no further copies.
#[test]
fn final_effect_rows_share_one_closed_iterator_artifact_family() {
    let raw = emit(
        "effect_instantiation_sharing",
        "fn main() -> [int] { [1, 2] |> concat([3, 4]) |> map(|x| x*x) }",
        MirOptimization::Disabled,
    );
    let headers = raw
        .lines()
        .filter(|line| line.starts_with("fn "))
        .collect::<Vec<_>>();
    let value = headers
        .iter()
        .filter(|line| line.contains("Value<std::MapIterator"))
        .copied()
        .collect::<Vec<_>>();
    let iterator = headers
        .iter()
        .filter(|line| line.contains("Iterator<std::MapIterator"))
        .copied()
        .collect::<Vec<_>>();
    let from_iterator = headers
        .iter()
        .filter(|line| line.contains("FromIterator<") && line.contains("std::MapIterator"))
        .copied()
        .collect::<Vec<_>>();
    let value_entry_count = CompilerSession::new()
        .std_module()
        .get_trait_str("Value")
        .unwrap()
        .runtime_dictionary_entry_count();
    assert!(
        value
            .iter()
            .chain(iterator.iter())
            .chain(from_iterator.iter())
            .all(|line| line.contains("int ! ()>")),
        "expected only closed families:\nvalue={value:#?}\niterator={iterator:#?}\n\
         from_iterator={from_iterator:#?}"
    );
    assert_eq!(
        value.len(),
        value_entry_count,
        "expected one closed Value family:\n{value:#?}"
    );
    assert_eq!(
        iterator.len(),
        1,
        "expected one Iterator thunk:\n{iterator:#?}"
    );
    assert_eq!(
        from_iterator.len(),
        1,
        "expected one FromIterator thunk:\n{from_iterator:#?}"
    );
    assert!(
        value
            .iter()
            .chain(iterator.iter())
            .chain(from_iterator.iter())
            .all(|line| !line.contains("-1(")),
        "the retained artifacts must not acquire a collision suffix:\nvalue={value:#?}\n\
         iterator={iterator:#?}\nfrom_iterator={from_iterator:#?}"
    );
}

/// Trait-output inference may consider an effectful application before defaulting establishes the
/// mapper's final pure effect. Those provisional queries must not leave a second generated
/// dictionary family in the module: runtime dictionaries are materialized only from final HIR.
#[test]
fn provisional_effect_queries_do_not_materialize_trait_artifacts() {
    let src = "map([1, 2, 3], |x| x + 2)";
    let raw = emit(
        "delayed_trait_materialization",
        src,
        MirOptimization::Disabled,
    );
    let map_thunks = raw
        .lines()
        .filter(|line| {
            line.starts_with("fn std::Map<[std::int], std::int>::map#impl:")
                && line.contains("-thunk(")
        })
        .collect::<Vec<_>>();
    assert_eq!(
        map_thunks.len(),
        1,
        "only the final pure map application may materialize a dictionary method:\n{map_thunks:#?}"
    );
    // Hidden requirements may be fallible: they follow the adaptor impls' declared effects.
    assert!(
        map_thunks[0].contains("@arg let (int) -> int,"),
        "the retained map thunk must use the lambda's final pure effect:\n{}",
        map_thunks[0]
    );
}

/// A generic function passing its callback to an adaptor over a concrete input needs a dictionary
/// whose effects remain the callback's variable. Closing it at the implementation's least effects
/// would compile the callback's call as unable to fail.
#[test]
fn open_output_effects_keep_generated_dictionaries_open() {
    let raw = emit(
        "open_output_effects",
        "fn g(a: [int], f) { a |> filter(f) }\ng([1, 2], |x| idiv(x, 0) > 0)",
        MirOptimization::Disabled,
    );
    let filter_iterator_families = raw
        .lines()
        .filter(|line| {
            line.starts_with("fn std::Iterator<std::FilterIterator<") && line.contains("-thunk")
        })
        .collect::<Vec<_>>();
    assert_eq!(
        filter_iterator_families.len(),
        1,
        "expected one generated `next` for the open application:\n{filter_iterator_families:#?}"
    );
    assert!(
        filter_iterator_families[0].contains("std::int ! e₀>"),
        "the generated `next` must stay open in the callback's effect:\n{}",
        filter_iterator_families[0]
    );
}

/// Extracts one rendered function, excluding later functions in the module dump.
fn rendered_function<'a>(mir: &'a str, name: &str) -> &'a str {
    rendered_function_with_prefix(mir, &format!("{name}("))
}

/// Extracts one rendered function whose generated name begins with `prefix`. Generated impl names
/// end in a content hash, so callers intentionally identify only the stable semantic prefix.
fn rendered_function_with_prefix<'a>(mir: &'a str, prefix: &str) -> &'a str {
    let start = mir
        .find(&format!("fn {prefix}"))
        .unwrap_or_else(|| panic!("MIR does not contain function beginning `{prefix}`"));
    let rest = &mir[start..];
    rest.find("\nfn ").map_or(rest, |end| &rest[..end])
}

/// Counts `call` operations in rendered MIR.
fn calls(mir: &str) -> usize {
    mir.lines()
        .filter(|line| line.trim_start().starts_with("call "))
        .count()
}
/// Optimization is a per-session choice over shared module revisions: the standard library's
/// artifacts are reused across sessions, so a session that optimizes must not change what a
/// session that does not optimize executes, in either order.
#[test]
fn optimization_of_one_session_does_not_leak_into_another() {
    let (name, src) = CORPUS[1];

    let mut optimizing = session(MirOptimization::Enabled);
    let mut plain = session(MirOptimization::Disabled);

    let baseline = emit(name, src, MirOptimization::Disabled);
    let optimized_first = optimizing.emit_mir(name, src);
    let plain_after = plain.emit_mir(name, src);
    assert_ne!(
        optimized_first, baseline,
        "this snippet must be one optimization changes, or the test proves nothing"
    );
    assert_eq!(
        plain_after, baseline,
        "a session that does not optimize must still see raw MIR"
    );

    // And a session created after std was optimized still reads the raw bodies by default.
    let fresh = CompilerSession::new();
    assert_eq!(fresh.mir_optimization(), MirOptimization::Disabled);
}

#[test]
fn known_callback_arguments_specialize_without_inlining_the_caller() {
    let optimized = emit(
        "callback",
        r#"
        #[inline(never)] fn apply(f, x: int) -> int { let mut result = x; for i in (0..x) { result = f(result) }; result }
        #[inline(never)] fn inc(x: int) -> int { x + 1 }
        #[inline(never)] fn dec(x: int) -> int { x - 1 }
        fn up(x: int) -> int { apply(inc, x) }
        fn down(x: int) -> int { apply(dec, x) }
        fn dynamic(f, x: int) -> int { apply(f, x) }
    "#,
        MirOptimization::Enabled,
    );
    let copies = optimized
        .split("\nfn ")
        .filter(|body| body.starts_with("apply#spec:"))
        .collect::<Vec<_>>();
    assert_eq!(
        copies.len(),
        2,
        "distinct callbacks need distinct bodies: {optimized}"
    );
    assert!(
        copies
            .iter()
            .any(|body| body.contains("call callback::inc(")),
        "{optimized}"
    );
    assert!(
        copies
            .iter()
            .any(|body| body.contains("call callback::dec(")),
        "{optimized}"
    );
    assert!(
        copies.iter().all(|body| !body.contains("call %")),
        "{optimized}"
    );
    let dynamic = rendered_function_with_prefix(&optimized, "dynamic");
    assert!(dynamic.contains("call callback::apply("), "{dynamic}");
}

#[test]
fn callback_specializations_are_shared_across_call_sites() {
    let optimized = emit(
        "callback",
        r#"
        #[inline(never)] fn apply(f, x: int) -> int { let mut result = x; for i in (0..x) { result = f(result) }; result }
        #[inline(never)] fn inc(x: int) -> int { x + 1 }
        fn first(x: int) -> int { apply(inc, x) }
        fn second(x: int) -> int { apply(inc, x + 1) }
    "#,
        MirOptimization::Enabled,
    );
    assert_eq!(
        optimized.matches("\nfn apply#spec:").count(),
        1,
        "{optimized}"
    );
}

#[test]
fn generic_callback_recursion_retains_specialization_at_every_level() {
    let optimized = emit(
        "callback_recursion",
        r#"
        #[inline(never)] fn repeat(f, n: int, x) {
            if n == 0 { x } else { repeat(f, n - 1, f(x)) }
        }
        #[inline(never)] fn swapped(f, g, n: int, x) {
            if n == 0 { x } else { swapped(g, f, n - 1, f(x)) }
        }
        #[inline(never)] fn inc(x: int) -> int { x + 1 }
        #[inline(never)] fn dec(x: int) -> int { x - 1 }
        fn run(x: int) -> int { repeat(inc, 3, x) + swapped(inc, dec, 3, x) }
    "#,
        MirOptimization::Enabled,
    );
    for name in ["repeat", "swapped"] {
        let copies = optimized
            .split("\nfn ")
            .filter(|body| body.starts_with(&format!("{name}#spec:")))
            .collect::<Vec<_>>();
        assert!(!copies.is_empty(), "{optimized}");
        for body in copies {
            assert!(
                !body.contains(&format!("call callback_recursion::{name}(")),
                "generic recursion survives: {body}"
            );
            if name == "repeat" {
                assert!(
                    !body.contains("call %"),
                    "forwarded known callback must be direct: {body}"
                );
            }
            assert!(
                body.contains(&format!("call callback_recursion::{name}#spec:")),
                "specialized recursion missing: {body}"
            );
        }
    }
}

/// An adaptor consumed by a loop is built in the loop's frame: its fields split into locals, the
/// collection it would copy is borrowed from the parameter, and the non-capturing callback it
/// stores is a bare function, so the loop calls it directly.
#[test]
fn inlined_adaptors_borrow_their_collection_and_call_their_callback_directly() {
    for pipeline in [
        "filter(|row| len(row) > 0)",
        "map(|row| row)",
        "filter_map(|row| if len(row) > 0 { Some(row) } else { None })",
    ] {
        let optimized = emit(
            "adaptor",
            &format!(
                "fn view(rows: [[int]]) -> int {{ let mut n = 0; for row in iter(rows) |> {pipeline} {{ n += len(row) }}; n }}"
            ),
            MirOptimization::Enabled,
        );
        let view = rendered_function(&optimized, "view");
        assert!(
            !view.contains("clone [[int]]") && !view.contains("function_value_clone"),
            "{pipeline}: the collection must be borrowed and the callback not cloned:\n{view}"
        );
        // A `filter_map` callback that is not inlined returns its own copy of the element.
        assert!(
            pipeline.starts_with("filter_map") || !view.contains("clone [int]"),
            "{pipeline}: each element must be read in place:\n{view}"
        );
        assert!(
            !view.lines().any(|line| line.contains("call %")),
            "{pipeline}: the callback must be called directly:\n{view}"
        );
    }
}

/// A consumer such as `sum` copies the iterator it receives, which the caller then only drops at
/// exit: the copy becomes a move, and the moved collection is borrowed from the parameter. Each
/// element is then read in place, including one an accepting `filter` moves on to `map`.
#[test]
fn consumed_adaptors_move_their_iterator_and_borrow_their_collection() {
    for body in [
        "iter(rows) |> map(|row| len(row)) |> sum()",
        "iter(rows) |> filter(|row| len(row) > 0) |> map(|row| len(row)) |> sum()",
        "let lengths = rows |> map(|row| len(row)); len(lengths)",
    ] {
        let optimized = emit(
            "consumer",
            &format!("fn view(rows: [[int]]) -> int {{ {body} }}"),
            MirOptimization::Enabled,
        );
        let view = rendered_function(&optimized, "view");
        assert!(
            !view.lines().any(|line| {
                let line = line.trim_start();
                line.starts_with("clone [[int]]") || line.starts_with("clone MapIterator")
            }),
            "{body}: neither the iterator nor its collection may be cloned:\n{view}"
        );
        assert!(
            !view.contains("clone [int]"),
            "{body}: each element must be read in place:\n{view}"
        );
    }
}

/// A lambda in a generic function captures only that function's dictionaries, as `sum`'s folding
/// lambda does. Once those are constants, the closure is the lambda at its recorded instantiation:
/// it is called directly, specialized and inlined, and never built.
#[test]
fn closures_of_dictionaries_alone_are_called_directly() {
    for (name, source) in [
        (
            "sum",
            "fn view(rows: [[int]]) -> int { iter(rows) |> map(|row| len(row)) |> sum() }",
        ),
        (
            "local",
            "fn total(xs) { let add = |a, b| a + b; let mut t = 0; for x in xs { t = add(t, x) }; t }
            fn view(xs: [int]) -> int { total(xs) }",
        ),
    ] {
        let optimized = emit("evidence_closure", source, MirOptimization::Enabled);
        let view = rendered_function(&optimized, "view");
        assert!(
            !view.contains("build_closure") && !view.lines().any(|line| line.contains("call %")),
            "{name}: the closure must be neither built nor called indirectly:\n{view}"
        );
    }
}

/// A retained callee invoking a known capturing closure in a loop is specialized on the closure's
/// lambda: the specialization still receives the closure, reads its captures in place and calls
/// the lambda directly, which inlining then removes, dictionary calls included.
#[test]
fn known_capturing_callbacks_are_called_directly() {
    let source = "#[inline(never)] fn from_fn(n, f) {
            let mut data = [];
            for i in 0..n { array_append(data, f(i)) };
            data
        }
        fn scale(v, k) { from_fn(len(v), |i| v[i] * k) }
        fn view(v: [float], k: float) -> [float] { scale(v, k) }";
    let optimized = emit("known_closure", source, MirOptimization::Enabled);
    let specialized = rendered_function_with_prefix(&optimized, "from_fn#spec:");
    assert!(
        specialized.contains("closure_capture")
            && !specialized.lines().any(|line| line.contains("call %")),
        "the callback must be read in place and called directly:\n{specialized}"
    );
}

/// Once inlining has brought an adaptor's call through its callback into the function building the
/// closure, that call is direct too, and the lambda is inlined with its dictionary calls.
#[test]
fn local_capturing_closures_are_called_directly() {
    let source = "fn scaled(values, k) { values |> map(|x| x * k + 1) }
        fn view(v: [int], k: int) -> [int] { scaled(v, k) }";
    let optimized = emit("local_closure", source, MirOptimization::Enabled);
    let view = rendered_function(&optimized, "view");
    assert!(
        !view.lines().any(|line| line.contains("call %")),
        "the closure must be called directly and inlined:\n{view}"
    );
}

/// A `clone` names its `Value` method as a call names its callee, with the static evidence the
/// method's dictionary captured, so it is specialized on that evidence like a call: the copy reads
/// no dictionary entry, and so neither does the drop it makes.
#[test]
fn lifecycle_dispatches_are_specialized_on_static_evidence() {
    let source = "fn pair(v: [int]) -> ([int], [int]) { (v, v) }";
    let optimized = emit("lifecycle_dispatch", source, MirOptimization::Enabled);
    let pair = rendered_function(&optimized, "pair");
    assert!(
        pair.lines()
            .filter(|line| line.trim_start().starts_with("clone "))
            .all(|line| line.contains("#spec:") && !line.contains(" with (")),
        "the clones must name an evidence-free specialization:\n{pair}"
    );
    let start = optimized
        .lines()
        .position(|line| {
            line.starts_with("fn std::Value<[std::int]>::clone#impl") && line.contains("#spec:")
        })
        .expect("the clone method must be specialized");
    let specialized = optimized
        .lines()
        .skip(start)
        .take_while(|line| !line.is_empty())
        .collect::<Vec<_>>()
        .join("\n");
    assert!(
        !specialized.contains("dict_entry")
            && !specialized.lines().any(|line| line.contains("call %")),
        "the specialized method must dispatch nothing through its dictionaries:\n{specialized}"
    );
}

/// A generic type's `Value` method is generic over the impl's quantifiers, which a `clone` does not
/// record but its type determines: the method is specialized at the concrete type, and the element
/// copies it makes go direct with it.
#[test]
fn generic_lifecycle_methods_are_specialized_at_the_dispatched_type() {
    let source = "struct Wrap<T> { items: [T] }
        fn keep<T>(w: Wrap<T>) -> (Wrap<T>, Wrap<T>) { (w, w) }
        fn view(w: Wrap<float>) -> (Wrap<float>, Wrap<float>) { keep(w) }";
    let optimized = emit("generic_lifecycle", source, MirOptimization::Enabled);
    let view = rendered_function(&optimized, "view");
    let clones: Vec<_> = view
        .lines()
        .filter(|line| line.trim_start().starts_with("clone "))
        .collect();
    assert!(
        !clones.is_empty()
            && clones
                .iter()
                .all(|line| line.contains("-generic#spec:[float]") && !line.contains(" with (")),
        "the clones must name the method specialized at `float`:\n{view}"
    );
    let start = optimized
        .lines()
        .position(|line| {
            line.starts_with("fn std::Value<generic_lifecycle::Wrap<A>>::clone#impl:")
                && line.contains("-generic#spec:[float](")
        })
        .expect("the generic clone method must be specialized at `float`");
    let specialized = optimized
        .lines()
        .skip(start)
        .take_while(|line| !line.is_empty())
        .collect::<Vec<_>>()
        .join("\n");
    assert!(
        !specialized.contains("dict_entry")
            && !specialized.lines().any(|line| line.contains("call %")),
        "the specialized method must dispatch nothing through its dictionaries:\n{specialized}"
    );
}

/// Traversing a hash collection steps through its buckets with the generic `Value` impl of the
/// optional entry, closed over the key and value dictionaries at run time. Once those are
/// constants, the closed dictionary is static evidence: dropping and cloning a bucket are direct
/// calls. The bucket array, each bucket and each value are then read in place, although the
/// inlined `next` poisons execution rather than dropping them on its unchecked index's failure.
#[test]
fn hash_collection_traversals_read_entries_in_place() {
    for (name, body) in [
        (
            "for",
            "fn view(t: map<int, [int]>) -> int { let mut n = 0; for (k, v) in t { n += k + len(v) }; n }",
        ),
        (
            "fold",
            "fn view(t: map<int, [int]>) -> int { fold(t, 0, |n, e| n + e.0 + len(e.1)) }",
        ),
        (
            "string keys",
            "fn view(t: map<string, [int]>) -> int { let mut n = 0; for (k, v) in t { n += len(k) + len(v) }; n }",
        ),
        (
            "set",
            "fn view(s: set<[int]>) -> int { let mut n = 0; for v in s { n += len(v) }; n }",
        ),
    ] {
        let optimized = emit("hash_traversal", body, MirOptimization::Enabled);
        let view = rendered_function(&optimized, "view");
        assert!(
            !view.lines().any(|line| {
                let line = line.trim_start();
                line.starts_with("clone ") || line.contains("call %") || line.contains("dict_entry")
            }),
            "{name}: entries must be read in place, without dynamic dispatch:\n{view}"
        );
        assert!(
            !view.contains("build_dictionary"),
            "{name}: a dictionary closed over constants must be static:\n{view}"
        );
    }
}
