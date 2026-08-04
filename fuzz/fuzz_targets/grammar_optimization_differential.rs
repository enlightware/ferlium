#![no_main]
// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Differential fuzzing of the MIR optimization passes: a generated program must compute the same
//! thing, and fail the same way, with partial evaluation on as with it off.
//!
//! The test suite runs its ~870 snippets under both stages already; this reaches the shapes nobody
//! wrote by hand. See `doc/plans/partial-evaluation.md`.

use ferlium::{
    CompilationOutput, CompilerSession, ExecutionTarget, MirOptimization,
    compiler::error::RuntimeErrorKind,
    eval::RuntimeError,
    execution::{ExecutionLimits, ReferenceInterpreterLimits},
    hir::value::Value,
    module::{LocalFunctionId, ModuleId, Path},
};
use libfuzzer_sys::fuzz_target;

/// Tight enough that a generated program cannot spin, generous enough that most terminate.
fn limits() -> ReferenceInterpreterLimits {
    ReferenceInterpreterLimits::new(ExecutionLimits::new(32, Some(100_000)), 4_096)
}

fn run(
    session: &mut CompilerSession,
    optimization: MirOptimization,
    module_id: ModuleId,
    entry: LocalFunctionId,
) -> Result<Value, RuntimeError> {
    session.set_mir_optimization(optimization);
    session.run_entry_with_limits(ExecutionTarget::Mir, module_id, entry, vec![], limits())
}

/// Whether an outcome says nothing about optimization.
///
/// Optimization may change how much fuel and call depth a program consumes — sandbox policy rather
/// than source-visible semantics — so a run that hit a limit is not comparable with one that did
/// not. That is a documented difference, not a divergence.
fn hit_a_limit(result: &Result<Value, RuntimeError>) -> bool {
    matches!(
        result.as_ref().err().map(RuntimeError::kind),
        Some(RuntimeErrorKind::SandboxViolation(_))
    )
}

fuzz_target!(|tape: &[u8]| {
    let Some(source) = ferlium_fuzz::source_from_tape(tape) else {
        return;
    };

    let mut session = CompilerSession::new();
    let Ok(CompilationOutput { module_id, expr }) = session.compile_for(
        ExecutionTarget::Mir,
        &source,
        "fuzz.fer",
        Path::single_str("fuzz"),
    ) else {
        return;
    };
    // Only an expression is worth running: a generated module without one has nothing to compare.
    let Some(entry) = expr else {
        return;
    };

    let raw = run(&mut session, MirOptimization::Disabled, module_id, entry);
    let optimized = run(&mut session, MirOptimization::Enabled, module_id, entry);

    if hit_a_limit(&raw) || hit_a_limit(&optimized) {
        discard(raw);
        discard(optimized);
        return;
    }

    match (&raw, &optimized) {
        (Ok(raw_value), Ok(optimized_value)) => {
            // `Value` is not comparable, and rendering one needs a session that is borrowed here;
            // its `Debug` form is structural and enough to catch a divergence.
            let expected = format!("{raw_value:?}");
            let actual = format!("{optimized_value:?}");
            assert_eq!(
                actual, expected,
                "optimization changed the result of:\n{source}"
            );
        }
        (Err(raw_error), Err(optimized_error)) => {
            assert_eq!(
                optimized_error.kind(),
                raw_error.kind(),
                "optimization changed the failure of:\n{source}"
            );
        }
        (raw_result, optimized_result) => panic!(
            "optimization changed whether this program fails (raw: {raw_result:?}, optimized: \
             {optimized_result:?}):\n{source}"
        ),
    }

    discard(raw);
    discard(optimized);
});

/// `Value` is `ManuallyDrop`-based, so a run's result has to be released explicitly.
fn discard(result: Result<Value, RuntimeError>) {
    if let Ok(value) = result {
        value.discard_storage();
    }
}
