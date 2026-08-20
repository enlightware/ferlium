// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
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

use ferlium::{CompilerSession, MirOptimization, mir::pass::budget::INLINE_FUNCTION_GROWTH};

/// Snippets chosen to cover the operation and control-flow forms a rewrite must carry through:
/// calls, generics and dictionary passing, closures, aggregates, variants and matching, loops,
/// mutation, strings, and fallible operations.
const CORPUS: &[(&str, &str)] = &[
    ("literal", "fn main() -> int { 42 }"),
    ("arithmetic", "fn main() -> int { let x = 2 + 3; x * 7 }"),
    (
        "generic",
        "fn twice(f, x) { f(f(x)) }\nfn main() -> int { twice(|v| v + 1, 0) }",
    ),
    (
        "conditional",
        "fn main() -> int { let mut n = 0; if n == 0 { n = 1 } else { n = 2 }; n }",
    ),
    (
        "loop",
        "fn main() -> int { let mut sum = 0; for i in 0..5 { sum = sum + i }; sum }",
    ),
    (
        "tuple_and_record",
        "fn main() -> int { let t = (1, 2); let r = { a: t.0, b: t.1 }; r.a + r.b }",
    ),
    (
        "variant_match",
        "fn classify(v) { match v { Some(x) => x, None => 0 } }\n\
         fn main() -> int { classify(Some(3)) + classify(None) }",
    ),
    (
        "string",
        "fn main() -> string { let s = \"ab\"; string_concat(s, \"cd\") }",
    ),
    (
        "closure_capture",
        "fn main() -> int { let n = 5; let add = |x| x + n; add(1) + add(2) }",
    ),
    (
        "array",
        "fn main() -> int { let mut a = [1, 2, 3]; a[0] = 10; a[0] + a[2] }",
    ),
    // Indexing is source-fallible, so this lowers through `invoke` terminators and error edges.
    ("invoke", "fn main() -> int { let a = [1, 2]; a[0] + a[1] }"),
    // A fallible call whose arguments *are* known: it is a fold candidate in every respect except
    // that folding it would have to rewrite the `invoke` terminator's control flow.
    ("invoke_constant", "fn main() -> int { idiv(6, 3) }"),
    (
        "recursion",
        "fn fact(n) { if n <= 1 { 1 } else { n * fact(n - 1) } }\nfn main() -> int { fact(5) }",
    ),
];

fn session(optimization: MirOptimization) -> CompilerSession {
    let mut session = CompilerSession::new();
    session.set_mir_optimization(optimization);
    session
}

/// Emits the MIR of `src` under `optimization`, in a fresh session.
fn emit(name: &str, src: &str, optimization: MirOptimization) -> String {
    session(optimization).emit_mir(name, src)
}

/// Optimization respects its growth budget.
///
/// Inlining copies a callee's body into its caller, and constructive rewrites can introduce a few
/// setup operations, so "optimization never adds anything" is not true. What remains true, and is
/// what the stability requirement rests on, is that a function grows by at most
/// `INLINE_FUNCTION_GROWTH` operations over the whole of optimization, not per round or per site.
///
/// A panic here means a pass produced a function the verifier rejects — which is the real point of
/// running this over the whole corpus and the whole standard library.
#[test]
fn optimization_respects_its_growth_budget() {
    for (name, src) in CORPUS {
        let raw = operations_per_function(&emit(name, src, MirOptimization::Disabled));
        let optimized = operations_per_function(&emit(name, src, MirOptimization::Enabled));
        for (function, before) in raw {
            let Some(after) = optimized.get(&function) else {
                continue;
            };
            assert!(
                *after <= before + INLINE_FUNCTION_GROWTH,
                "optimizing `{name}` grew `{function}` from {before} to {after}, beyond the \
                 budget of {INLINE_FUNCTION_GROWTH}"
            );
        }
    }
}

/// Operation counts per rendered function, keyed by signature line.
fn operations_per_function(mir: &str) -> std::collections::HashMap<String, usize> {
    let mut counts = std::collections::HashMap::new();
    let mut current = String::new();
    for line in mir.lines() {
        if let Some(signature) = line.strip_prefix("fn ") {
            current = signature.split('(').next().unwrap_or(signature).to_string();
            counts.entry(current.clone()).or_insert(0);
        } else if line.starts_with("    ") && !line.trim_start().starts_with("b") {
            *counts.entry(current.clone()).or_insert(0) += 1;
        }
    }
    counts
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
        main.contains("to %p0"),
        "the folded result must reach the return place:\n{main}"
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
            && tuple.contains("call std::string_push_static_str")
            && !tuple.contains("call std::string_push_str"),
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
            clone.contains("memcpy %p0 to %p1"),
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
        "%r0: *int = subfield @c0 from %p1\n    %r1: *int = subfield @c0 from %p0\n    memcpy %r1 to %r0"
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

/// Inference reaches the iterator pipeline through several provisional caller-local effect rows,
/// but only the final elaborated application may retain runtime artifacts. Its remaining open
/// effect variables are alpha-canonicalized within the single generated family.
#[test]
fn final_effect_rows_only_materialize_one_iterator_artifact_family() {
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

    assert_eq!(
        value.len(),
        7,
        "expected one seven-entry Value family:\n{value:#?}"
    );
    assert_eq!(
        iterator.len(),
        1,
        "expected one thunk for the final effect row:\n{iterator:#?}"
    );
    assert_eq!(
        from_iterator.len(),
        1,
        "expected one thunk for the final effect row:\n{from_iterator:#?}"
    );
    assert!(
        value.iter().all(|line| !line.contains("e₂")),
        "canonical families must number their own variables from zero:\n{value:#?}"
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
    assert!(
        !map_thunks[0].contains("! fallible"),
        "the retained map thunk must use the lambda's final pure effect:\n{}",
        map_thunks[0]
    );

    let optimized = emit(
        "delayed_trait_materialization",
        src,
        MirOptimization::Enabled,
    );
    let map_specializations = optimized
        .lines()
        .filter(|line| {
            line.starts_with("fn Map<[A], B>::map#impl:") && line.contains("#spec:[int, int]")
        })
        .collect::<Vec<_>>();
    assert_eq!(
        map_specializations.len(),
        1,
        "an orphaned provisional thunk must not request another map specialization:\n\
         {map_specializations:#?}"
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
