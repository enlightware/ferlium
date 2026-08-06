// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Inlining: replacing a call with the callee's own operations.
//!
//! Inlining pays twice. It removes the call itself, which in an interpreter costs frame setup and
//! argument binding; and it hands folding a body whose arguments are known, since a callee's
//! parameters are opaque to the analysis until the caller's operands are substituted for them. It is
//! also what makes devirtualization possible: a dictionary parameter bound to a constant dictionary
//! turns the callee's `dict_entry`s into known functions, and its indirect calls into direct ones.
//!
//! A call site is either an ordinary `call` operation or an `invoke` terminator — the latter being
//! how a call to a source-fallible callee is represented. Both are inlined, and the callee may have
//! any control-flow shape:
//!
//! - **the call site's block is split.** For a `call` operation, the operations after it and the
//!   block's terminator move to a continuation block; for an `invoke`, the continuation already
//!   exists as the terminator's normal successor. The call's block then jumps into the callee's
//!   entry. Splitting is unconditional, so a callee that needed none arrives as three blocks joined
//!   by jumps; the driver's merge step collapses those again (see [`super::merge_function`]).
//! - **parameters are substituted by the caller's operands.** A call's operands are exactly the
//!   callee's parameters in signature order (`@extra`, `@arg`, `@ret`), so the substitution is
//!   positional. It is also why inlining hands folding known arguments: what was `%pN` becomes the
//!   caller's place.
//! - **blocks and registers are renumbered** into the caller and **constants merged** into its pool.
//!   Both are allocated before anything is copied, because an operand may name a value or a block
//!   that does not precede its use in block order.
//! - **every exit of the callee is rewired.** A `return` becomes a jump to the continuation, and a
//!   `propagate_error` a jump to the call site's error successor — which exists precisely when the
//!   callee can propagate, since such a callee is called through an `invoke`.
//! - **the body is bracketed by `stack_save`/`stack_restore`**, because the callee's `alloca`s now
//!   live in the caller's frame and nothing else would reclaim them at the point its frame used to
//!   end. Each rewired exit restores; a `failure_during_cleanup` does not, because poisoning hands
//!   what is left to runtime reclamation.
//!
//! Two restrictions remain, both refusals rather than approximations: a callee whose types are not
//! all concrete (see [`check_inlinable`]), and a call site inside a cleanup path when the callee has
//! error flow of its own (see [`cleanup_blocks`]).

#![allow(dead_code)]

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    CompilerSession, Location,
    compiler::MirOptimization,
    mir::{
        self, BlockId, Function, Operation, OperationKind,
        edit::{FunctionEdit, successors},
        terminator::{Terminator, TerminatorKind},
    },
    module::{FunctionId, ModuleEnv, ModuleId, id::Id},
    types::{r#type::CallResultConvention, type_like::TypeLike},
};

use super::{Specializations, budget, function_size};

/// Where the call to inline sits in the caller.
#[derive(Clone, Copy)]
enum Site {
    /// An ordinary `call` operation, at `index` in `block`.
    Operation { block: BlockId, index: usize },
    /// The `invoke` terminator of `block`: a call to a source-fallible callee.
    Terminator { block: BlockId },
}

impl Site {
    fn block(self) -> BlockId {
        match self {
            Site::Operation { block, .. } | Site::Terminator { block } => block,
        }
    }

    /// Whether the site has an error successor for a callee's `propagate_error` to jump to.
    fn has_error_successor(self) -> bool {
        matches!(self, Site::Terminator { .. })
    }
}

/// A call site to replace with its callee's body.
struct Inlining {
    site: Site,
    callee: FunctionId,
}

/// Why one call site was not inlined.
///
/// Kept apart from [`NotFoldable`](crate::mir::const_eval::NotFoldable) rather than merged into it:
/// the two passes refuse for different reasons, and the report says which pass is speaking. The
/// overlap is real but small — a callee that is not statically known blocks both.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum NotInlinable {
    /// The callee is not statically known, so there is no body to copy.
    CalleeNotDirect,
    /// The callee is a native, or otherwise has no MIR body.
    NoBody,
    /// The callee returns through a convention the splice does not handle.
    UnsupportedConvention,
    /// The callee is generic: its operations carry types written in its own type environment, and
    /// copying them without substituting the call site's instantiation would reinterpret them.
    /// Specialization is what would lift this.
    Generic,
    /// The callee is recursive, which its call-depth guard is the local evidence of.
    Recursive,
    /// The callee contains a scoped accessor, which the caller's frame does not stand in for.
    UnsupportedShape,
    /// The site is inside a cleanup path and the callee has error flow of its own, so copying it
    /// would shift its failure states by one level.
    InCleanupPath,
    /// The callee is larger than [`budget::INLINE_CALLEE_OPERATIONS`].
    CalleeTooLarge,
    /// Inlining here would exceed [`budget::INLINE_FUNCTION_GROWTH`] for this caller.
    GrowthBudgetExhausted,
}

impl NotInlinable {
    /// A short phrase naming the reason, for the optimization report.
    ///
    /// User-visible: prefer describing what is missing over naming an internal mechanism, and keep
    /// the wording stable — people grep for these.
    pub(crate) fn description(self) -> &'static str {
        match self {
            Self::CalleeNotDirect => "callee not statically known",
            Self::NoBody => "callee has no body to copy",
            Self::UnsupportedConvention => "result convention is not supported",
            Self::Generic => "callee is generic",
            Self::Recursive => "callee is recursive",
            Self::UnsupportedShape => "callee contains a scoped accessor",
            Self::InCleanupPath => "call site is on a cleanup path",
            Self::CalleeTooLarge => "callee is over the size budget",
            Self::GrowthBudgetExhausted => "caller is at its growth budget",
        }
    }
}

/// Why one call site was not inlined, and where it is.
pub(crate) struct Refusal {
    pub site: Location,
    pub callee: Option<FunctionId>,
    pub reason: NotInlinable,
}

/// Inlines what can be inlined in `func`, returning a rewritten function if anything was.
pub(crate) fn inline_function(
    func: &Function,
    original_size: usize,
    env: ModuleEnv<'_>,
    session: &CompilerSession,
    module_id: ModuleId,
    specializations: &Specializations,
) -> Option<Function> {
    let _ = module_id;
    let sites = plan_inlinings(
        func,
        original_size,
        session,
        Some(specializations),
        &mut None,
    );
    if sites.is_empty() {
        return None;
    }

    let mut edit = FunctionEdit::new(func.clone());
    // Later sites first, so splicing one does not move the ones still to be done: within a block
    // that is the terminator before the operations, and the operations in decreasing index — which
    // is the reverse of the order they were planned in.
    for inlining in sites.into_iter().rev() {
        let body = callee_body(session, inlining.callee, Some(specializations))
            .expect("planning read this body from the same artifacts");
        inline_at(&mut edit, &body, inlining.site, env);
    }
    // Splicing always splits the call site's block and joins the pieces with jumps, so a callee
    // that needed no split arrives as three blocks. Collapse them here, in this pass's own edit,
    // rather than in a separate driver step: the step costs an extra clone and an
    // extra verification per round, and measured worse than the merge saves.
    edit.merge_blocks_into_predecessors();
    // A splice appends the continuation and the callee's blocks, which can leave a block that uses
    // a value before the block defining it. Dominance is unaffected, but block order is what MIR's
    // consumers walk, so canonical order is restored before the function is closed.
    edit.reorder_blocks_in_reverse_postorder();
    Some(edit.finish(env))
}

/// Chooses the call sites to inline.
///
/// `original_size` is the function's size before *any* round ran, so the growth budget bounds the
/// whole of optimization rather than each round — otherwise a function could grow by the budget
/// again on every round, and the cap would only bound growth per round.
///
/// `refusals`, when present, collects why each call site was left alone — the optimization report
/// runs this over an already-optimized body precisely so its answers cannot drift from the pass's.
fn plan_inlinings(
    func: &Function,
    original_size: usize,
    session: &CompilerSession,
    specializations: Option<&Specializations>,
    refusals: &mut Option<&mut Vec<Refusal>>,
) -> Vec<Inlining> {
    let mut sites = Vec::new();
    let mut size = function_size(func);
    let cleanup = cleanup_blocks(func);

    for block in func.blocks() {
        let in_cleanup = cleanup.contains(&block);
        let basic = func.block(block);
        // Operations first and the terminator last, which is the order they occur in: the reverse
        // of this list is the order they can be spliced in without moving one another.
        let candidates = basic
            .operations()
            .iter()
            .enumerate()
            .map(|(index, operation)| (Site::Operation { block, index }, operation))
            .chain(match &basic.terminator().kind {
                TerminatorKind::Invoke { operation, .. } => {
                    Some((Site::Terminator { block }, operation))
                }
                _ => None,
            });

        for (site, operation) in candidates {
            let OperationKind::Call { ty, .. } = &operation.kind else {
                continue;
            };
            let callee = match &operation.operands[0] {
                mir::Value::Function(callee) => Some(*callee),
                _ => None,
            };
            let mut refuse = |reason: NotInlinable| {
                if let Some(refusals) = refusals.as_mut() {
                    refusals.push(Refusal {
                        site: operation.span,
                        callee,
                        reason,
                    });
                }
            };

            if ty.result_convention != CallResultConvention::Value {
                refuse(NotInlinable::UnsupportedConvention);
                continue;
            }
            let Some(callee) = callee else {
                refuse(NotInlinable::CalleeNotDirect);
                continue;
            };
            let Some(body) = callee_body(session, callee, specializations) else {
                refuse(NotInlinable::NoBody);
                continue;
            };
            if let Err(reason) = check_inlinable(&body, site.has_error_successor(), in_cleanup) {
                refuse(reason);
                continue;
            }
            let callee_size = function_size(&body);
            // The call goes; the callee's operations arrive, plus a `stack_save` and one
            // `stack_restore` per exit — bounded by the block count.
            let cost = callee_size + body.blocks().count() + 1;
            if callee_size > budget::INLINE_CALLEE_OPERATIONS {
                refuse(NotInlinable::CalleeTooLarge);
                continue;
            }
            if size + cost > original_size + budget::INLINE_FUNCTION_GROWTH {
                refuse(NotInlinable::GrowthBudgetExhausted);
                continue;
            }
            size += cost;
            sites.push(Inlining { site, callee });
        }
    }
    sites
}

/// Classifies every call site of `func` that inlining left alone, for the optimization report.
pub(crate) fn refusals_of(func: &Function, session: &CompilerSession) -> Vec<Refusal> {
    let mut refusals = Vec::new();
    // Measured against the body as it stands: the question the report answers is whether *another*
    // round would inline this site, not what the budget was when optimization started.
    plan_inlinings(
        func,
        function_size(func),
        session,
        None,
        &mut Some(&mut refusals),
    );
    refusals
}

/// The callee's body, read from the raw stage.
///
/// Deliberately raw rather than optimized: the driver reads raw bodies everywhere so that a result
/// never depends on the order functions are optimized in. Folding runs over the inlined body
/// afterwards, which recovers most of what an already-simplified callee would have given.
///
/// A specialization the optimizer created has no raw *artifact* — it exists only in the stage being
/// built — so its equivalent comes from the table, which keeps each body as it was created, before
/// the worklist optimized it. Same rule, same reason. `specializations` is `None` for the
/// optimization report, which runs after the table is consumed into the artifacts; a specialization
/// then reports as having no body, which is a cosmetic gap in the report rather than a decision.
fn callee_body(
    session: &CompilerSession,
    callee: FunctionId,
    specializations: Option<&Specializations>,
) -> Option<Function> {
    if let Some(specializations) = specializations
        && specializations.is_specialization(callee.function)
    {
        return specializations.raw_body(callee.function).cloned();
    }
    session
        .mir_artifacts_for(callee.module, MirOptimization::Disabled)?
        .get(callee.function)
        .cloned()
}

/// The blocks a source failure is already in flight in — everything reachable from an error edge.
///
/// A callee's body means something different there. Copied into a block that is already propagating,
/// the callee's own error edges would enter the caller one failure deeper than they were written
/// for: what the callee spells `propagate_error` would be reached after a second failure, where MIR
/// requires `failure_during_cleanup`. Rather than shift a body's failure states — a rewrite with no
/// measured demand behind it — a callee with error flow of its own is refused at such a site.
///
/// Normal and error flow never join (the verifier proves it), so plain reachability from the error
/// edges is exactly the set of blocks reached with a failure in flight.
fn cleanup_blocks(func: &Function) -> FxHashSet<BlockId> {
    let mut cleanup = FxHashSet::default();
    let mut worklist: Vec<BlockId> = func
        .blocks()
        .filter_map(|block| match &func.block(block).terminator().kind {
            TerminatorKind::Invoke { error, .. } => Some(*error),
            _ => None,
        })
        .collect();
    while let Some(block) = worklist.pop() {
        if !cleanup.insert(block) {
            continue;
        }
        worklist.extend(successors(func.block(block).terminator()));
    }
    cleanup
}

/// Whether this callee can be copied into this call site, and what stops it if not.
///
/// The subtle refusal is the generic one. An operation carries types — `clone_closure_env { ty }`,
/// `alloca { ty }`, a call's `CallImplType` — and those are written in the *callee's* type
/// environment. Copying them into a caller with a different instantiation silently reinterprets
/// them: inlining a generic `Value<A>::clone` into a concrete caller makes its `A` mean whatever
/// `A` happens to be there. Making that sound requires substituting the call site's instantiation
/// through the body, which is what specialization does — so only callees that carry no type
/// variables at all are inlined.
///
/// **A dictionary parameter is not itself a reason to refuse**, which is what lets a specialization
/// be inlined. Splicing binds `@extra` parameters to the caller's operands like any other, and a
/// genuinely generic body is already refused above: its evidence parameter's own type mentions the
/// variables it is evidence for, so it is not constant. What remains is a body whose dictionary
/// parameters are concrete — a specialization, whose evidence has already been bound to constants
/// inside it, leaving those parameters unread.
///
/// A recursive callee carries a call-depth guard, so the presence of `check_call_depth` *is* the
/// recursion test — a local check on the callee, which is also what bounds inlining. Scoped
/// accessors are excluded wholesale: a `yield` suspends into a driver that resumes it, which the
/// caller's frame does not stand in for.
fn check_inlinable(
    body: &Function,
    has_error_successor: bool,
    in_cleanup: bool,
) -> Result<(), NotInlinable> {
    let generic = body
        .parameters()
        .iter()
        .any(|parameter| !parameter.ty.is_constant());
    if generic {
        return Err(NotInlinable::Generic);
    }
    if body.blocks().next().is_none() {
        return Err(NotInlinable::UnsupportedShape);
    }
    for block in body.blocks() {
        let block = body.block(block);
        if matches!(block.terminator().kind, TerminatorKind::Yield { .. })
            || block.operations().iter().any(|operation| {
                matches!(
                    operation.kind,
                    OperationKind::Project { .. } | OperationKind::EndProject
                )
            })
        {
            return Err(NotInlinable::UnsupportedShape);
        }
        if block
            .operations()
            .iter()
            .any(|operation| matches!(operation.kind, OperationKind::CheckCallDepth))
        {
            return Err(NotInlinable::Recursive);
        }
    }

    let error_flow = body.blocks().any(|block| {
        matches!(
            body.block(block).terminator().kind,
            TerminatorKind::Invoke { .. }
                | TerminatorKind::PropagateError
                | TerminatorKind::FailureDuringCleanup
        )
    });
    if error_flow && in_cleanup {
        return Err(NotInlinable::InCleanupPath);
    }
    // A callee that propagates needs somewhere to propagate to. It always has one in practice — a
    // propagating callee is source-fallible, and so called through an `invoke` — but the rewrite
    // relies on it, so it is checked rather than assumed.
    let propagates = body.blocks().any(|block| {
        matches!(
            body.block(block).terminator().kind,
            TerminatorKind::PropagateError
        )
    });
    if propagates && !has_error_successor {
        return Err(NotInlinable::UnsupportedShape);
    }
    Ok(())
}

/// Replaces the call at `site` with `body`, rewired into the caller.
fn inline_at(edit: &mut FunctionEdit, body: &Function, site: Site, env: ModuleEnv<'_>) {
    // Take the call apart, and decide where the callee's exits lead.
    let (call, normal, error) = match site {
        Site::Operation { block, index } => {
            let caller = edit.block_mut(block);
            let mut tail = caller.operations.split_off(index);
            let call = tail.remove(0);
            let terminator = caller.terminator.clone();
            // What followed the call becomes the continuation the callee's `return`s jump to.
            let continuation = edit.add_block(terminator);
            edit.block_mut(continuation).operations = tail;
            (call, continuation, None)
        }
        Site::Terminator { block } => {
            let TerminatorKind::Invoke {
                operation,
                normal,
                error,
            } = &edit.block(block).terminator.kind
            else {
                unreachable!("an invoke site was planned on a block that no longer invokes")
            };
            (operation.clone(), *normal, Some(*error))
        }
    };

    let span = call.span;
    // The callee's `alloca`s land in the caller's frame; the bracket is what reclaims them where
    // the callee's own frame used to end.
    let marker_id = edit.new_value();
    let mut marker = Operation::stack_save(span);
    marker.assign_result_id(Some(marker_id));
    edit.block_mut(site.block()).operations.push(marker);

    let arguments = call.operands[1..].to_vec();
    let mut copier = Copier {
        body,
        arguments,
        marker: mir::Value::Register(marker_id),
        normal,
        error,
        blocks: FxHashMap::default(),
        registers: FxHashMap::default(),
        constants: FxHashMap::default(),
    };
    let entry = copier.copy_into(edit, env);
    edit.block_mut(site.block()).terminator = Terminator::goto(span, entry);
}

/// The state of one splice: what the callee's identities become in the caller.
struct Copier<'a> {
    body: &'a Function,
    /// The call's operands, which are the callee's parameters in signature order.
    arguments: Vec<mir::Value>,
    /// The stack marker every rewired exit restores to.
    marker: mir::Value,
    /// Where a `return` continues.
    normal: BlockId,
    /// Where a `propagate_error` continues, when the site has an error successor.
    error: Option<BlockId>,
    blocks: FxHashMap<BlockId, BlockId>,
    registers: FxHashMap<mir::ValueId, mir::ValueId>,
    constants: FxHashMap<usize, mir::Value>,
}

impl Copier<'_> {
    /// Copies the whole body into `edit`, returning the caller's block that is its entry.
    fn copy_into(&mut self, edit: &mut FunctionEdit, env: ModuleEnv<'_>) -> BlockId {
        // Blocks and result identities are allocated up front: an operand may name a value defined
        // in a block that dominates its use without preceding it in block order, and a terminator
        // may target a block that has not been copied yet.
        for source in self.body.blocks() {
            let placeholder = Terminator::ret(self.body.block(source).terminator().span);
            let copy = edit.add_block(placeholder);
            self.blocks.insert(source, copy);
            let block = self.body.block(source);
            let invoked = match &block.terminator().kind {
                TerminatorKind::Invoke { operation, .. } => Some(operation),
                _ => None,
            };
            for operation in block.operations().iter().chain(invoked) {
                if let Some(result) = operation.result_id() {
                    let fresh = edit.new_value();
                    self.registers.insert(result, fresh);
                }
            }
        }

        // Built aside and installed afterwards, because copying an operation needs the editor
        // mutably — a constant of the callee's pool is interned into the caller's as it is met.
        let mut built = Vec::with_capacity(self.blocks.len());
        for source in self.body.blocks() {
            let block = self.body.block(source);
            let mut operations = Vec::with_capacity(block.operations().len() + 1);
            for operation in block.operations() {
                let copy = self.operation(edit, operation, &env);
                operations.push(copy);
            }
            let terminator = self.terminator(edit, block.terminator(), &mut operations, &env);
            built.push((self.blocks[&source], operations, terminator));
        }
        for (id, operations, terminator) in built {
            let block = edit.block_mut(id);
            block.operations = operations;
            block.terminator = terminator;
        }

        self.blocks[&self.body.entry()]
    }

    fn operand(
        &mut self,
        edit: &mut FunctionEdit,
        operand: &mir::Value,
        env: &ModuleEnv<'_>,
    ) -> mir::Value {
        match operand {
            mir::Value::Parameter(id) => self.arguments[id.as_index()].clone(),
            mir::Value::Register(id) => mir::Value::Register(self.registers[id]),
            mir::Value::Constant(id) => {
                if let Some(known) = self.constants.get(&id.as_index()) {
                    return known.clone();
                }
                let constant = self.body.constant(*id);
                let copy = mir::Value::Constant(edit.add_constant(
                    constant.ty,
                    constant.representation.clone(),
                    env,
                ));
                self.constants.insert(id.as_index(), copy.clone());
                copy
            }
            other => other.clone(),
        }
    }

    fn operation(
        &mut self,
        edit: &mut FunctionEdit,
        operation: &Operation,
        env: &ModuleEnv<'_>,
    ) -> Operation {
        let operands = operation
            .operands
            .iter()
            .map(|operand| self.operand(edit, operand, env))
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let mut copy = Operation::from_parts(operation.span, operands, operation.kind.clone());
        if let Some(result) = operation.result_id() {
            copy.assign_result_id(Some(self.registers[&result]));
        }
        copy
    }

    /// Copies a terminator, appending to `operations` whatever the rewired exit needs first.
    fn terminator(
        &mut self,
        edit: &mut FunctionEdit,
        terminator: &Terminator,
        operations: &mut Vec<Operation>,
        env: &ModuleEnv<'_>,
    ) -> Terminator {
        let span = terminator.span;
        match &terminator.kind {
            TerminatorKind::Goto { target } => Terminator::goto(span, self.blocks[target]),
            TerminatorKind::CondBr {
                condition,
                then_target,
                else_target,
            } => {
                let condition = self.operand(edit, condition, env);
                Terminator::cond_br(
                    span,
                    condition,
                    self.blocks[then_target],
                    self.blocks[else_target],
                )
            }
            TerminatorKind::Invoke {
                operation,
                normal,
                error,
            } => {
                let operation = self.operation(edit, operation, env);
                Terminator::invoke(span, operation, self.blocks[normal], self.blocks[error])
            }
            // Both exits leave the callee's storage behind in the caller's frame, so both restore
            // before continuing where the call site did.
            TerminatorKind::Return => {
                operations.push(Operation::stack_restore(span, self.marker.clone()));
                Terminator::goto(span, self.normal)
            }
            TerminatorKind::PropagateError => {
                operations.push(Operation::stack_restore(span, self.marker.clone()));
                let error = self
                    .error
                    .expect("a callee that propagates is inlined only at a site that can");
                Terminator::goto(span, error)
            }
            // Poisoning hands the frame to runtime reclamation, so there is nothing to restore.
            TerminatorKind::FailureDuringCleanup => Terminator::failure_during_cleanup(span),
            TerminatorKind::Yield { .. } => {
                unreachable!("a callee containing a yield is not inlined")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{CompilerSession, MirOptimization};

    fn optimized(src: &str) -> String {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        session.emit_mir("inline", src)
    }

    fn body_of<'a>(module: &'a str, name: &str) -> &'a str {
        module
            .split(&format!("fn {name}"))
            .nth(1)
            .unwrap_or_else(|| panic!("module has no `{name}`:\n{module}"))
    }

    /// What inlining is for: the callee's body arrives with the caller's operands substituted in,
    /// so its argument becomes known and folding finishes the job.
    #[test]
    fn inlining_a_callee_makes_its_argument_known() {
        let module = optimized(
            "fn double(x: int) -> int { x + x }\nfn main() -> int { let n = 21; double(n) }",
        );
        let main = body_of(&module, "main");
        assert!(
            !main.contains("call "),
            "the call must be inlined and then folded away:\n{main}"
        );
        assert!(
            main.contains("= 42"),
            "the result must be constant:\n{main}"
        );
    }

    /// A generic callee is not inlined: its operations carry types written in its own type
    /// environment, which would mean something else in the caller.
    ///
    /// The caller is generic too, so that specialization cannot reach the call: it records a
    /// variable instantiation, which is not something to specialize at. A *concrete* caller has its
    /// call specialized and the concrete copy inlined, which is the whole point of Phase 4.
    #[test]
    fn a_generic_callee_is_not_inlined() {
        let module = optimized("fn identity(x) { x }\nfn use_it(n) { identity(n) }");
        let caller = body_of(&module, "use_it");
        assert!(
            caller.contains("call inline::identity"),
            "a generic callee must be left alone:\n{caller}"
        );
    }

    /// A callee with a branch needs its blocks copied and its several `return`s rewired to a
    /// continuation. With the argument unknown the branch survives folding, so what is left is the
    /// inlined control flow itself.
    #[test]
    fn a_branching_callee_is_inlined() {
        let module = optimized(
            "fn clamp(x: int) -> int { if x > 10 { 10 } else { x } }\n\
             fn use_it(n: int) -> int { clamp(n) + 1 }",
        );
        let caller = body_of(&module, "use_it");
        assert!(
            !caller.contains("call inline::clamp"),
            "the branching callee must be inlined:\n{caller}"
        );
        assert!(
            caller.contains("condbr"),
            "its branch must arrive in the caller:\n{caller}"
        );
    }

    /// A source-fallible callee is called through an `invoke`, and its `propagate_error` becomes a
    /// jump to that invoke's error successor.
    #[test]
    fn a_fallible_callee_is_inlined_at_its_invoke() {
        let module = optimized(
            "fn half(x: int) -> int { idiv(x, 2) }\nfn use_it(n: int) -> int { half(n) }",
        );
        let caller = body_of(&module, "use_it");
        assert!(
            !caller.contains("call inline::half"),
            "the fallible callee must be inlined:\n{caller}"
        );
        assert!(
            caller.contains("invoke"),
            "the callee's own fallible call keeps its invoke:\n{caller}"
        );
    }

    /// A loop is a callee like any other once blocks are copied: its back edge is a block target,
    /// remapped like the rest.
    #[test]
    fn a_looping_callee_is_inlined() {
        let module = optimized(
            "fn count_to(n: int) -> int { let mut sum = 0; for i in 0..n { sum = sum + i }; sum }\n\
             fn use_it(n: int) -> int { count_to(n) }",
        );
        let caller = body_of(&module, "use_it");
        assert!(
            !caller.contains("call inline::count_to"),
            "the looping callee must be inlined:\n{caller}"
        );
    }
}
