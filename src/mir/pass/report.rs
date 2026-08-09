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

use ustr::Ustr;

use crate::{
    Location, MirOptimization,
    compiler::{CompilerSession, Specialization},
    format::FormatWith,
    mir::{
        self, Function, Operation, OperationKind, const_eval::NotFoldable,
        terminator::TerminatorKind,
    },
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

/// One body the optimizer specialized, priced against what specializing it achieved.
///
/// Unlike a [`Remark`], this reports an optimization the optimizer *took*. It is here because
/// specialization is the one pass that trades code size for anything: folding and inlining are
/// bounded by budgets stated up front, while a specialization is a whole extra body, kept forever,
/// justified only by what substituting its types removed. Cost and payoff side by side are what a
/// cost model would have to weigh, and neither is otherwise observable — a specialized body is in
/// no source file and, deliberately, in neither stage's paired tables.
///
/// The payoff is three counts rather than one because substitution pays three ways, and a
/// specialization can win on any of them alone. See [`SpecializationRemark::payoff`].
pub struct SpecializationRemark {
    /// The generated name, which carries the instantiation where it was short enough to render.
    pub name: Ustr,
    /// The function this was specialized from.
    pub original: FunctionId,
    /// Operations in the original's raw body: what asking for this copy duplicated, and the only
    /// size a cost model could consult, since the decision is taken against the raw stage.
    pub original_size: usize,
    /// Operations in the original after *it* was optimized, where that is known.
    ///
    /// Only a diagnostic, and deliberately not a candidate predictor — it is unavailable at the
    /// moment of the decision, and depends on optimization order besides. It is here to separate
    /// two stories that `size` alone conflates: a specialization that is large because its body
    /// genuinely is, and one that is large because being concrete made it a target the inliner
    /// then filled. Only the second would be answered by re-pricing inlining rather than
    /// specialization.
    pub original_optimized_size: Option<usize>,
    /// Operations in the specialized body, after it was itself optimized. The real cost, since
    /// substitution deletes the clones, drops and layout witnesses it makes redundant.
    pub size: usize,
    /// Calls with no statically known callee in the original's raw body.
    pub indirect_before: usize,
    /// Calls with no statically known callee left in the specialized body. The drop from
    /// `indirect_before` is the devirtualization actually realized, rather than the one
    /// `worth_specializing` predicted from the presence of a dictionary read.
    pub indirect_after: usize,
    /// Calls of any kind in the original's raw body.
    pub calls_before: usize,
    /// Calls of any kind left in the specialized body.
    ///
    /// Reported next to the indirect counts because they answer different questions and a
    /// specialization can win on either. Devirtualizing a call leaves the count alone; turning a
    /// `Value::clone` into a `memcpy` lowers it without resolving anything. Reading only one of them
    /// is how a specialization that pays its way looks like dead weight.
    pub calls_after: usize,
    /// Dictionary-reading operations in the original's raw body.
    pub dictionary_reads_before: usize,
    /// Dictionary-reading operations left in the specialized body — the third payoff, and the one
    /// that catches a dropped layout witness, which changes neither call count.
    pub dictionary_reads_after: usize,
}

impl SpecializationRemark {
    /// Indirect calls this specialization resolved.
    ///
    /// Saturating rather than signed: a specialization that inlined a callee can end up with more
    /// indirect calls than its original had, and "resolved none" is the honest reading of that.
    pub fn resolved(&self) -> usize {
        self.indirect_before.saturating_sub(self.indirect_after)
    }

    /// Everything this specialization removed that not knowing the type had cost: calls that are
    /// gone, calls that are no longer indirect, and dictionary reads that are gone.
    ///
    /// A deliberately flat sum of three things a backend would weigh very differently. It exists to
    /// separate a specialization that bought *nothing* from one that bought *something* — which is
    /// the distinction a refusal can be built on — and not to rank the ones that did.
    pub fn payoff(&self) -> usize {
        self.calls_before.saturating_sub(self.calls_after)
            + self.resolved()
            + self
                .dictionary_reads_before
                .saturating_sub(self.dictionary_reads_after)
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
    /// Every body the optimizer specialized, in the order it created them.
    ///
    /// These are counted in neither figure above, which pair the two stages and so cover only what
    /// the source declared. A specialization exists in the optimized stage alone.
    pub specializations: Vec<SpecializationRemark>,
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
    specializations: &[Specialization],
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
            inline::refusals_of(optimized_body, env, session)
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
        specializations: specializations
            .iter()
            .map(|specialization| specialization_remark(session, specialization))
            .collect(),
    }
}

/// Prices one specialization against the original it was copied from.
///
/// The original is read from *its own* module's raw stage, which need not be the module being
/// reported on: cross-module specialization is what puts a `std` generic in a user module's table.
/// A missing original leaves the sizes at zero rather than panicking — the report is opt-in output,
/// and must not be the thing that brings a session down.
fn specialization_remark(
    session: &CompilerSession,
    specialization: &Specialization,
) -> SpecializationRemark {
    let body_of = |stage| {
        session
            .mir_artifacts_for(specialization.original.module, stage)
            .and_then(|artifacts| artifacts.get(specialization.original.function).cloned())
    };
    let raw = body_of(MirOptimization::Disabled);
    let optimized = body_of(MirOptimization::Enabled);
    // The `_before` figures come from the *optimized* original wherever there is one, because the
    // question is what specializing bought over what the call site would otherwise have reached —
    // and what it would otherwise have reached is a body the optimizer had already been over.
    // Measuring against the raw original instead credits specialization with every fold and inline
    // the original got anyway, which is most of the difference on a body of any size.
    let baseline = optimized.as_ref().or(raw.as_ref());
    SpecializationRemark {
        name: specialization.name,
        original: specialization.original,
        original_size: raw.as_ref().map_or(0, super::function_size),
        original_optimized_size: optimized.as_ref().map(super::function_size),
        size: super::function_size(&specialization.body),
        indirect_before: baseline.map_or(0, indirect_calls),
        indirect_after: indirect_calls(&specialization.body),
        calls_before: baseline.map_or(0, call_sites),
        calls_after: call_sites(&specialization.body),
        dictionary_reads_before: baseline.map_or(0, dictionary_reads),
        dictionary_reads_after: dictionary_reads(&specialization.body),
    }
}

/// Every `call` operation of a function, including one in an `invoke` terminator.
fn calls(func: &Function) -> impl Iterator<Item = &Operation> {
    func.blocks().flat_map(|block| {
        let block = func.block(block);
        block
            .operations()
            .iter()
            .chain(match &block.terminator().kind {
                TerminatorKind::Invoke { operation, .. } => Some(operation),
                _ => None,
            })
            .filter(|operation| matches!(operation.kind, OperationKind::Call { .. }))
    })
}

/// Counts the `call` operations of a function, including one in an `invoke` terminator.
fn call_sites(func: &Function) -> usize {
    calls(func).count()
}

/// Counts the calls whose callee is not statically known — what devirtualization removes.
fn indirect_calls(func: &Function) -> usize {
    calls(func)
        .filter(|operation| !matches!(operation.operands[0], mir::Value::Function(_)))
        .count()
}

/// Counts operations that consume evidence because a type's behavior or layout is not static.
///
/// The residue of not knowing a type: every entry read that a call goes through, and every layout
/// witness an allocation or move consults. Substitution is what removes them, and their count is
/// the one benefit measure that covers all three of specialization's payoffs rather than only
/// devirtualization — a `Value::clone` that becomes a `memcpy`, or a dynamic-layout `alloca` that
/// becomes static, shows up here and nowhere else.
fn dictionary_reads(func: &Function) -> usize {
    func.blocks()
        .flat_map(|block| {
            let block = func.block(block);
            block
                .operations()
                .iter()
                .chain(match &block.terminator().kind {
                    TerminatorKind::Invoke { operation, .. } => Some(operation),
                    _ => None,
                })
        })
        .filter(|operation| match operation.kind {
            OperationKind::DictEntry { .. } => true,
            OperationKind::Alloca { .. } => operation.operands.len() == 1,
            OperationKind::Move => operation.operands.len() == 3,
            _ => false,
        })
        .count()
}

impl FormatWith<ModuleEnv<'_>> for OptimizationReport {
    fn fmt_with(&self, f: &mut fmt::Formatter<'_>, env: &ModuleEnv<'_>) -> fmt::Result {
        writeln!(
            f,
            "{} call sites before optimization, {} after",
            self.call_sites_before, self.call_sites_after
        )?;
        if !self.specializations.is_empty() {
            let operations: usize = self.specializations.iter().map(|s| s.size).sum();
            let inert = self
                .specializations
                .iter()
                .filter(|s| s.payoff() == 0)
                .count();
            writeln!(
                f,
                "  {} specializations, {operations} operations, {inert} buying nothing",
                self.specializations.len()
            )?;
            // Costliest per unit of payoff first: a cost model has to reject from this end, so this
            // is the order in which to read the list.
            let mut ranked: Vec<&SpecializationRemark> = self.specializations.iter().collect();
            ranked.sort_by_key(|s| std::cmp::Reverse(s.size / s.payoff().max(1)));
            for s in ranked {
                let original = match s.original_optimized_size {
                    Some(optimized) => format!("{} raw, {optimized} optimized", s.original_size),
                    None => format!("{} raw", s.original_size),
                };
                writeln!(
                    f,
                    "    {:>6}  {} ops (original {original}), \
                     calls {}->{} ({} indirect->{}), dict reads {}->{}",
                    s.size / s.payoff().max(1),
                    s.size,
                    s.calls_before,
                    s.calls_after,
                    s.indirect_before,
                    s.indirect_after,
                    s.dictionary_reads_before,
                    s.dictionary_reads_after,
                )?;
                writeln!(f, "            {}", s.name)?;
            }
        }
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

    /// A generic callee is the refusal specialization exists to lift, so it gets its own reason
    /// rather than being folded into a general "shape" bucket.
    ///
    /// The caller is deliberately generic too. A *concrete* caller now has its call specialized,
    /// which lifts this refusal and replaces it with one about the specialization — so the snippet
    /// has to be one specialization cannot reach: a caller that forwards its own quantifier records
    /// a variable instantiation, which is not something to specialize at.
    #[test]
    fn a_generic_callee_is_reported_as_generic() {
        let (report, rendered) = report_for("fn identity(x) { x }\nfn use_it(n) { identity(n) }");
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

    /// A layout witness is evidence just as a dictionary entry is. It is carried as the extra
    /// operand of a dynamic `alloca` or `move`, so counting only `dict_entry` operations reports a
    /// specialization such as `swap<int>` as buying nothing even though substitution makes its
    /// temporary statically sized.
    #[test]
    fn specialization_payoff_counts_removed_layout_witnesses() {
        let (report, rendered) = report_for(
            "fn swap(a, i, j) { let temp = a[i]; a[i] = a[j]; a[j] = temp }\n\
             fn swap_ints(a: [int], i: int, j: int) { let mut t = a; swap(t, i, j); t }",
        );
        let specialization = report
            .specializations
            .iter()
            .find(|specialization| specialization.name.starts_with("swap#spec:"))
            .unwrap_or_else(|| panic!("swap must specialize:\n{rendered}"));
        assert!(
            specialization.dictionary_reads_before > specialization.dictionary_reads_after,
            "the removed layout witness must be counted as specialization payoff:\n{rendered}"
        );
        assert!(specialization.payoff() > 0, "{rendered}");
    }
}
