// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! What the optimizer did, and what it declined to do.
//!
//! Two audiences want this. A user who annotates a hot path to make it foldable needs to know
//! whether it worked, and the optimized MIR is a poor way to ask. We need the aggregate: what
//! fraction of call sites fold, and what dominates the refusals — which is what sizes the work that
//! would lift them. LLVM calls the same idea optimization remarks; the vocabulary is deliberate.
//!
//! **It is never a diagnostic.** An unfolded call is ordinary, not a problem; this is opt-in output.
//! And it reports what folded as well as what did not, because the ratio is the point — a list of
//! refusals alone cannot distinguish "not folded" from "not a call site".
//!
//! **Nothing is instrumented to produce it.** The report is *derived*, on request, from the two
//! artifact stages a module already keeps: what disappeared between the raw and optimized bodies
//! was folded, and each call that remains is re-classified by the folding pass's own predicate — so
//! the answers cannot drift from what the pass actually decided. A session that never asks pays
//! nothing.

use std::fmt;

use crate::{
    Location,
    compiler::CompilerSession,
    format::FormatWith,
    mir::{Function, OperationKind, const_eval::NotFoldable, terminator::TerminatorKind},
    module::{FunctionId, ModuleEnv, ModuleId},
};

use super::fold;

/// The pass a remark came from.
///
/// Only folding reports today. The field exists so that inlining and specialization — which will
/// want to say the same kind of thing about the same call sites — extend this rather than growing a
/// second, parallel surface.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum OptimizationPass {
    Fold,
}

impl fmt::Display for OptimizationPass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Fold => write!(f, "fold"),
        }
    }
}

/// One call site the optimizer left alone, and why.
pub struct Remark {
    pub site: Location,
    /// The callee, when it is statically known — it is not, precisely when that is the reason.
    pub callee: Option<FunctionId>,
    pub pass: OptimizationPass,
    reason: NotFoldable,
}

impl Remark {
    /// A short phrase naming the reason.
    pub fn reason(&self) -> &'static str {
        self.reason.description()
    }
}

/// What optimizing a module achieved, and what it declined.
///
/// The two counts are stated rather than a single "folded" figure, because inlining copies a
/// callee's calls into its caller: the difference between them is a net, not a count of folds, and
/// it can be negative. Recovering a true fold count needs the passes to record their own rewrites;
/// until then the report says what it can actually measure.
pub struct OptimizationReport {
    /// Call sites the module had before optimization.
    pub call_sites_before: usize,
    pub remarks: Vec<Remark>,
}

impl OptimizationReport {
    /// Call sites that remain — every one of which has a remark saying why.
    pub fn call_sites_after(&self) -> usize {
        self.remarks.len()
    }

    /// Reasons and their counts, most frequent first — the summary line of the whole exercise.
    pub fn reasons(&self) -> Vec<(&'static str, usize)> {
        let mut counts: Vec<(&'static str, usize)> = Vec::new();
        for remark in &self.remarks {
            match counts.iter_mut().find(|(name, _)| *name == remark.reason()) {
                Some((_, count)) => *count += 1,
                None => counts.push((remark.reason(), 1)),
            }
        }
        counts.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(b.0)));
        counts
    }
}

/// Builds the report for `module_id`, in `session`.
///
/// Both artifact stages must be prepared; the session query that wraps this ensures it.
pub(crate) fn build(
    session: &CompilerSession,
    module_id: ModuleId,
    raw: &[Option<Function>],
    optimized: &[Option<Function>],
    env: ModuleEnv<'_>,
) -> OptimizationReport {
    let mut call_sites_before = 0usize;
    let mut remarks = Vec::new();

    for (raw_body, optimized_body) in raw.iter().zip(optimized) {
        let (Some(raw_body), Some(optimized_body)) = (raw_body, optimized_body) else {
            continue;
        };
        call_sites_before += call_sites(raw_body);

        let mut refusals = Vec::new();
        let plan = fold::plan_folds(
            optimized_body,
            env,
            session,
            module_id,
            &mut Some(&mut refusals),
        );
        remarks.extend(refusals.into_iter().map(|refusal| Remark {
            site: refusal.site,
            callee: refusal.callee,
            pass: OptimizationPass::Fold,
            reason: refusal.reason,
        }));
        // A call the pass would still fold means optimization stopped before reaching it, which is
        // the round budget talking. Worth saying out loud: it is the one refusal we control
        // directly.
        for _ in 0..plan.foldable_calls() {
            remarks.push(Remark {
                site: Location::new_synthesized(),
                callee: None,
                pass: OptimizationPass::Fold,
                reason: NotFoldable::RoundsExhausted,
            });
        }
    }

    OptimizationReport {
        call_sites_before,
        remarks,
    }
}

/// Counts the `call` operations of a function, including one in an `invoke` terminator.
fn call_sites(func: &Function) -> usize {
    func.blocks()
        .map(|block| {
            let block = func.block(block);
            let in_operations = block
                .operations()
                .iter()
                .filter(|operation| matches!(operation.kind, OperationKind::Call { .. }))
                .count();
            let in_terminator = match &block.terminator().kind {
                TerminatorKind::Invoke { operation, .. } => {
                    usize::from(matches!(operation.kind, OperationKind::Call { .. }))
                }
                _ => 0,
            };
            in_operations + in_terminator
        })
        .sum()
}

impl FormatWith<ModuleEnv<'_>> for OptimizationReport {
    fn fmt_with(&self, f: &mut fmt::Formatter<'_>, env: &ModuleEnv<'_>) -> fmt::Result {
        writeln!(
            f,
            "{} call sites before optimization, {} after",
            self.call_sites_before,
            self.call_sites_after()
        )?;
        if self.remarks.is_empty() {
            writeln!(f, "  everything folded")?;
            return Ok(());
        }
        writeln!(f, "  {} not folded", self.remarks.len())?;
        for (reason, count) in self.reasons() {
            writeln!(f, "  {count:>6}  {reason}")?;
        }
        for remark in &self.remarks {
            let callee = match remark.callee {
                Some(id) => crate::mir::Value::Function(id).format_with(env).to_string(),
                None => "<indirect>".to_string(),
            };
            let span = remark.site.span();
            writeln!(
                f,
                "    {}..{}  {}  [{}] {}",
                span.start(),
                span.end(),
                callee,
                remark.pass,
                remark.reason()
            )?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        CompilerSession, ExecutionTarget, MirOptimization, format::FormatWith, module::Path,
    };

    fn report_for(src: &str) -> (crate::mir::pass::report::OptimizationReport, String) {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let module_id = session
            .compile_for(
                ExecutionTarget::Mir,
                src,
                "report",
                Path::single_str("report"),
            )
            .expect("must compile")
            .module_id;
        let report = session.optimization_report(module_id);
        let module = session.expect_fresh_module(module_id);
        let env = crate::module::ModuleEnv::new(module, session.raw_modules());
        let rendered = report.format_with(&env).to_string();
        (report, rendered)
    }

    /// Everything folds in a constant expression, so nothing remains to remark on.
    #[test]
    fn a_fully_folded_function_has_no_remarks() {
        let (report, rendered) = report_for("fn main() -> int { let x = 2 + 3; x * 7 }");
        assert!(report.remarks.is_empty(), "{rendered}");
        assert_eq!(report.call_sites_after(), 0);
        assert!(report.call_sites_before > 0, "{rendered}");
        assert!(rendered.contains("everything folded"), "{rendered}");
    }

    /// A call on a runtime value cannot fold, and the report says which argument-shaped reason it
    /// was — the distinction that decides whether inlining or specialization would lift it.
    #[test]
    fn an_unknown_argument_is_reported_as_such() {
        let (report, rendered) = report_for("fn twice(n: int) -> int { n + n }");
        let reasons: Vec<&str> = report.reasons().into_iter().map(|(name, _)| name).collect();
        assert!(
            reasons.contains(&"argument not known"),
            "expected an unknown-argument remark:\n{rendered}"
        );
    }

    /// The rendering leads with the counts, since that is what both audiences read first.
    #[test]
    fn the_summary_states_both_counts() {
        let (report, rendered) =
            report_for("fn f(n: int) -> int { n + 1 }\nfn main() -> int { 2 + 3 }");
        assert_eq!(report.call_sites_after(), report.remarks.len());
        assert!(report.call_sites_before > 0);
        assert!(
            rendered.contains("call sites before optimization"),
            "{rendered}"
        );
    }
}
