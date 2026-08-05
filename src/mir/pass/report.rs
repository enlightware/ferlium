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
//! artifact stages a module already keeps: their call sites are counted, and each call that remains
//! is re-classified by each pass's own predicate — so the answers cannot drift from what the passes
//! actually decided. A session that never asks pays nothing.
//!
//! **Each pass speaks for itself.** A site both passes declined carries a remark from each, because
//! "why was this not evaluated away?" and "why was the callee not copied in?" have different
//! answers and different remedies — a native folds readily and can never be inlined.

use std::fmt;

use crate::{
    Location,
    compiler::CompilerSession,
    format::FormatWith,
    mir::{Function, OperationKind, const_eval::NotFoldable, terminator::TerminatorKind},
    module::{FunctionId, ModuleEnv, ModuleId},
};

use super::{fold, inline, inline::NotInlinable};

/// The pass a remark came from.
///
/// A call site left alone gets a remark from each pass that declined it, so the two questions —
/// "why was this not evaluated away?" and "why was the callee not copied in?" — are answered
/// separately. They have different answers and different remedies; a native, for instance, can
/// never be inlined but folds readily.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum OptimizationPass {
    Fold,
    Inline,
}

impl OptimizationPass {
    pub const ALL: [Self; 2] = [Self::Fold, Self::Inline];
}

impl fmt::Display for OptimizationPass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Fold => write!(f, "fold"),
            Self::Inline => write!(f, "inline"),
        }
    }
}

/// Why a pass left a call site alone. Each pass has its own vocabulary.
enum RemarkReason {
    Fold(NotFoldable),
    Inline(NotInlinable),
}

/// One call site a pass left alone, and why.
pub struct Remark {
    pub site: Location,
    /// The callee, when it is statically known — it is not, precisely when that is the reason.
    pub callee: Option<FunctionId>,
    pub pass: OptimizationPass,
    reason: RemarkReason,
}

impl Remark {
    /// A short phrase naming the reason.
    pub fn reason(&self) -> &'static str {
        match self.reason {
            RemarkReason::Fold(reason) => reason.description(),
            RemarkReason::Inline(reason) => reason.description(),
        }
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
    /// Call sites that remain. Counted rather than derived from the remarks: a site that neither
    /// pass could take carries one remark from each.
    pub call_sites_after: usize,
    pub remarks: Vec<Remark>,
}

impl OptimizationReport {
    /// Reasons and their counts for one pass, most frequent first — the summary line of the whole
    /// exercise.
    pub fn reasons(&self, pass: OptimizationPass) -> Vec<(&'static str, usize)> {
        let mut counts: Vec<(&'static str, usize)> = Vec::new();
        for remark in self.remarks.iter().filter(|remark| remark.pass == pass) {
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
    let mut call_sites_after = 0usize;
    let mut remarks = Vec::new();

    for (raw_body, optimized_body) in raw.iter().zip(optimized) {
        let (Some(raw_body), Some(optimized_body)) = (raw_body, optimized_body) else {
            continue;
        };
        call_sites_before += call_sites(raw_body);
        call_sites_after += call_sites(optimized_body);

        remarks.extend(
            inline::refusals_of(optimized_body, session)
                .into_iter()
                .map(|refusal| Remark {
                    site: refusal.site,
                    callee: refusal.callee,
                    pass: OptimizationPass::Inline,
                    reason: RemarkReason::Inline(refusal.reason),
                }),
        );

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
            reason: RemarkReason::Fold(refusal.reason),
        }));
        // A call the pass would still fold means optimization stopped before reaching it, which is
        // the round budget talking. Worth saying out loud: it is the one refusal we control
        // directly.
        for _ in 0..plan.foldable_calls() {
            remarks.push(Remark {
                site: Location::new_synthesized(),
                callee: None,
                pass: OptimizationPass::Fold,
                reason: RemarkReason::Fold(NotFoldable::RoundsExhausted),
            });
        }
    }

    OptimizationReport {
        call_sites_before,
        call_sites_after,
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
            self.call_sites_before, self.call_sites_after
        )?;
        if self.remarks.is_empty() {
            writeln!(f, "  everything folded")?;
            return Ok(());
        }
        for pass in OptimizationPass::ALL {
            let reasons = self.reasons(pass);
            if reasons.is_empty() {
                continue;
            }
            let total: usize = reasons.iter().map(|(_, count)| count).sum();
            writeln!(f, "  {total} sites declined by {pass}")?;
            for (reason, count) in reasons {
                writeln!(f, "  {count:>6}  {reason}")?;
            }
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
    use super::OptimizationPass;
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
        assert_eq!(report.call_sites_after, 0);
        assert!(report.call_sites_before > 0, "{rendered}");
        assert!(rendered.contains("everything folded"), "{rendered}");
    }

    /// A call on a runtime value cannot fold, and the report says which argument-shaped reason it
    /// was — the distinction that decides whether inlining or specialization would lift it.
    #[test]
    fn an_unknown_argument_is_reported_as_such() {
        let (report, rendered) = report_for("fn twice(n: int) -> int { n + n }");
        let reasons: Vec<&str> = report
            .reasons(OptimizationPass::Fold)
            .into_iter()
            .map(|(name, _)| name)
            .collect();
        assert!(
            reasons.contains(&"argument is a parameter"),
            "expected an unknown-argument remark:\n{rendered}"
        );
    }

    /// The unknown-argument bucket is subdivided by what would lift it, so the two commonest cases
    /// must not land in the same one: `n` is a parameter, which specialization reaches, while the
    /// result of a call that itself refused is merely downstream of that refusal and needs nothing
    /// new. Counting them together is what made the bucket uninformative.
    #[test]
    fn unknown_arguments_are_split_by_what_would_lift_them() {
        let (report, rendered) = report_for(
            "fn opaque(n: int) -> int { n + 1 }\n\
             fn twice(n: int) -> int { opaque(n) + opaque(n) }",
        );
        let reasons: Vec<&str> = report
            .reasons(OptimizationPass::Fold)
            .into_iter()
            .map(|(name, _)| name)
            .collect();
        assert!(
            reasons.contains(&"argument is a parameter"),
            "the parameter case must be named:\n{rendered}"
        );
        assert!(
            reasons.contains(&"argument comes from a call that did not fold"),
            "the downstream case must be named separately:\n{rendered}"
        );
    }

    /// A call site declined by both passes is reported by both, in each pass's own vocabulary: a
    /// native folds when its arguments are known but can never be inlined, and the report has to
    /// say which of the two is the missing piece.
    #[test]
    fn a_remaining_call_is_classified_by_each_pass() {
        let (report, rendered) = report_for("fn twice(n: int) -> int { n + n }");
        let inline: Vec<&str> = report
            .reasons(OptimizationPass::Inline)
            .into_iter()
            .map(|(name, _)| name)
            .collect();
        assert!(
            inline.contains(&"callee has no body to copy"),
            "a native callee is not inlinable:\n{rendered}"
        );
        let fold: Vec<&str> = report
            .reasons(OptimizationPass::Fold)
            .into_iter()
            .map(|(name, _)| name)
            .collect();
        assert!(
            fold.contains(&"argument is a parameter"),
            "and folding refuses it for its own reason:\n{rendered}"
        );
    }

    /// A generic callee is the refusal Phase 4 exists to lift, so it gets its own reason rather
    /// than being folded into a general "shape" bucket.
    #[test]
    fn a_generic_callee_is_reported_as_generic() {
        let (report, rendered) =
            report_for("fn identity(x) { x }\nfn use_it(n: int) -> int { identity(n) }");
        let inline: Vec<&str> = report
            .reasons(OptimizationPass::Inline)
            .into_iter()
            .map(|(name, _)| name)
            .collect();
        assert!(
            inline.contains(&"callee is generic"),
            "expected a generic-callee remark:\n{rendered}"
        );
    }

    /// The rendering leads with the counts, since that is what both audiences read first.
    #[test]
    fn the_summary_states_both_counts() {
        let (report, rendered) =
            report_for("fn f(n: int) -> int { n + 1 }\nfn main() -> int { 2 + 3 }");
        assert!(report.call_sites_after > 0);
        assert!(report.call_sites_before > 0);
        assert!(
            rendered.contains("call sites before optimization"),
            "{rendered}"
        );
    }
}
