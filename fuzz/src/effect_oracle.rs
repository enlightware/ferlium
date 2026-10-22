// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Runs a generated effect program on every reference backend and checks the soundness oracles.
//!
//! A source failure escaping code compiled as unable to fail panics inside the MIR interpreters
//! (`a plain MIR operation raised a source failure`) or surfaces as an `EffectViolation`; both are
//! findings. Beyond that, every backend must agree, every rendering variant must agree, and a
//! program whose entry is typed as unable to fail must not fail.

use crate::effects::{EffectProgram, Variant};
use ferlium::{
    CompilerSession, ExecutionTarget, MirOptimization,
    compiler::error::RuntimeErrorKind,
    eval::RuntimeError,
    execution::{ExecutionLimits, ReferenceInterpreterLimits},
    module::Path,
};

/// The observable outcome of a run.
#[derive(Clone, Debug, PartialEq)]
pub enum Outcome {
    Value(isize),
    Failure(RuntimeErrorKind),
    /// A sandbox limit was hit: not comparable across backends.
    Limit,
}

/// What checking one program found, when it found nothing wrong.
#[derive(Debug)]
pub enum Report {
    /// The program was rejected; carries the error's variant name and its rendering.
    Rejected { category: String, message: String },
    /// The program ran; carries its outcome and whether its entry was typed as able to fail.
    Ran { outcome: Outcome, may_fail: bool },
}

const MODES: [(ExecutionTarget, MirOptimization, MirOptimization, &str); 5] = [
    (
        ExecutionTarget::Hir,
        MirOptimization::Disabled,
        MirOptimization::Enabled,
        "HIR",
    ),
    (
        ExecutionTarget::Mir,
        MirOptimization::Disabled,
        MirOptimization::Enabled,
        "MIR",
    ),
    (
        ExecutionTarget::Mir,
        MirOptimization::Enabled,
        MirOptimization::Enabled,
        "optimized MIR",
    ),
    (
        ExecutionTarget::PhysicalMir,
        MirOptimization::Enabled,
        MirOptimization::Disabled,
        "unoptimized physical MIR",
    ),
    (
        ExecutionTarget::PhysicalMir,
        MirOptimization::Enabled,
        MirOptimization::Enabled,
        "physical MIR",
    ),
];

/// Tight enough that a generated program cannot spin, generous enough that all terminate.
fn limits() -> ReferenceInterpreterLimits {
    ReferenceInterpreterLimits::new(ExecutionLimits::new(64, Some(1_000_000)), 4_096)
}

/// Compiles and runs `source` on every backend; panics on a finding.
pub fn check_source(source: &str) -> Report {
    let mut session = CompilerSession::new();
    let output = match session.compile(source, "effects.fer", Path::single_str("effects")) {
        Ok(output) => output,
        Err(error) => {
            let message = format!("{:?}", error.into_inner());
            let category = message
                .split(|c: char| !c.is_alphanumeric() && c != '_')
                .next()
                .unwrap_or_default()
                .to_string();
            return Report::Rejected { category, message };
        }
    };
    let entry = output
        .expr
        .expect("generated programs end with an expression");
    let may_fail = !session
        .expect_fresh_module(output.module_id)
        .get_function_by_id(entry)
        .expect("the entry is a function of its module")
        .definition
        .ty_scheme
        .ty()
        .effects
        .cannot_fail();

    let mut reference: Option<(Outcome, &str)> = None;
    for (target, optimization, physical_optimization, label) in MODES {
        session.set_mir_optimization(optimization);
        session.set_physical_mir_optimization(physical_optimization);
        let result =
            session.run_entry_with_limits(target, output.module_id, entry, vec![], limits());
        let error = result.as_ref().err().map(|error| format!("{error:?}"));
        let outcome = outcome(result);
        if let Outcome::Failure(kind) = &outcome {
            assert!(
                !matches!(kind, RuntimeErrorKind::EffectViolation),
                "{label}: a source failure escaped code typed as unable to fail:\n{source}"
            );
        }
        if outcome == Outcome::Limit {
            continue;
        }
        match &reference {
            None => reference = Some((outcome, label)),
            Some((expected, expected_label)) => assert_eq!(
                &outcome, expected,
                "{label} disagrees with {expected_label} ({error:?}) on:\n{source}"
            ),
        }
    }
    let outcome = reference.map_or(Outcome::Limit, |(outcome, _)| outcome);
    if let Outcome::Failure(RuntimeErrorKind::SourceFailure(_)) = outcome {
        assert!(
            may_fail,
            "the entry is typed as unable to fail, but fails with {outcome:?}:\n{source}"
        );
    }
    Report::Ran { outcome, may_fail }
}

fn outcome(result: Result<ferlium::hir::value::Value, RuntimeError>) -> Outcome {
    match result {
        Ok(value) => {
            let n = *value
                .as_primitive_ty::<isize>()
                .expect("generated programs compute an int");
            value.discard_storage();
            Outcome::Value(n)
        }
        Err(error) => match error.kind() {
            RuntimeErrorKind::SandboxViolation(_) => Outcome::Limit,
            kind => Outcome::Failure(kind),
        },
    }
}

/// Checks every rendering variant of `program`; they must all compile alike and agree.
pub fn check_program(program: &EffectProgram) -> Report {
    let variants = [
        Variant::default(),
        Variant {
            rename: true,
            reverse: true,
        },
    ];
    let base_source = program.render(variants[0]);
    let base = check_source(&base_source);
    for variant in &variants[1..] {
        let source = program.render(*variant);
        let report = check_source(&source);
        match (&base, &report) {
            (Report::Rejected { .. }, Report::Rejected { .. }) => {}
            (
                Report::Ran {
                    outcome: a,
                    may_fail: a_may_fail,
                },
                Report::Ran {
                    outcome: b,
                    may_fail: b_may_fail,
                },
            ) => {
                // Inferred effects must not depend on names or on cache population order, whatever
                // a run observes.
                assert_eq!(
                    a_may_fail, b_may_fail,
                    "renaming and reordering changed whether the entry may fail:\n{base_source}\nvariant:\n{source}"
                );
                if *a != Outcome::Limit && *b != Outcome::Limit {
                    assert_eq!(
                        a, b,
                        "renaming and reordering changed the outcome of:\n{base_source}\nvariant:\n{source}"
                    );
                }
            }
            _ => panic!(
                "renaming and reordering changed whether this compiles ({base:?} versus \
                 {report:?}):\n{base_source}\nvariant:\n{source}"
            ),
        }
    }
    base
}
