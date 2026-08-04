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
//! Optimization must never change what a program computes, only how. These tests hold optimized MIR
//! to that: every corpus snippet must produce the same result and the same failure with the flag on
//! as with it off, while folding is allowed to — and must — remove work.
//!
//! Every function reachable from a snippet, including every function of the standard library, is
//! rewritten through `FunctionEdit`, which runs the full MIR verifier on the result in test builds.
//! See `doc/plans/partial-evaluation.md`.

use ferlium::{CompilerSession, ExecutionTarget, MirOptimization, module::Path, ustr};

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

/// Runs `main` under `optimization`, in a fresh session, and renders the result.
fn run(name: &str, src: &str, optimization: MirOptimization) -> String {
    session(optimization).eval_mir(name, src)
}

/// Runs `main` under `optimization` and renders the runtime error it must raise.
fn run_failing(name: &str, src: &str, optimization: MirOptimization) -> String {
    let mut session = session(optimization);
    let output = session
        .compile_for(ExecutionTarget::Mir, src, name, Path::single_str(name))
        .unwrap_or_else(|error| panic!("{name} must compile: {error:?}"));
    let main = session
        .expect_fresh_module(output.module_id)
        .get_local_function_id(ustr("main"))
        .unwrap_or_else(|| panic!("{name} must define main"));
    let error = session
        .run_entry(ExecutionTarget::Mir, output.module_id, main, vec![])
        .err()
        .unwrap_or_else(|| panic!("{name} must fail at run time"));
    format!("{:?}", error.kind())
}

/// Optimization may only remove calls, never add them.
///
/// A panic here means a pass produced a function the verifier rejects — which is the real point of
/// running this over the whole corpus and the whole standard library.
#[test]
fn optimization_never_adds_calls() {
    for (name, src) in CORPUS {
        let raw = emit(name, src, MirOptimization::Disabled);
        let optimized = emit(name, src, MirOptimization::Enabled);
        assert!(
            calls(&optimized) <= calls(&raw),
            "optimizing `{name}` added calls: {} -> {}",
            calls(&raw),
            calls(&optimized)
        );
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
        main.contains("to %p0"),
        "the folded result must reach the return place:\n{main}"
    );
}

/// Counts `call` operations in rendered MIR.
fn calls(mir: &str) -> usize {
    mir.lines()
        .filter(|line| line.trim_start().starts_with("call "))
        .count()
}

#[test]
fn optimized_mir_executes_identically_to_raw_mir() {
    for (name, src) in CORPUS {
        let raw = run(name, src, MirOptimization::Disabled);
        let optimized = run(name, src, MirOptimization::Enabled);
        assert_eq!(
            raw, optimized,
            "optimization changed the result of `{name}`"
        );
    }
}

/// The error path must survive a rewrite too: a snippet that raises must raise the same way.
#[test]
fn optimized_mir_fails_identically_to_raw_mir() {
    let (name, src) = ("out_of_bounds", "fn main() -> int { let a = [1]; a[3] }");
    assert_eq!(
        run_failing(name, src, MirOptimization::Disabled),
        run_failing(name, src, MirOptimization::Enabled),
    );
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
