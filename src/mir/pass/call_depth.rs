// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Remove checks made unnecessary by known callees or an earlier check in the same frame.

use crate::{
    FxHashMap,
    mir::{
        BlockId, Function, OperationKind, dominance::Dominance, edit::FunctionEdit,
        terminator::TerminatorKind,
    },
    module::{FunctionId, ModuleEnv, id::Id},
};

use super::{SemanticCallees, budget, will_return::operation_calls_only};

pub(super) fn simplify_checks(
    body: &Function,
    env: ModuleEnv<'_>,
    callees: SemanticCallees<'_>,
) -> Option<Function> {
    let checks = body
        .blocks()
        .map(|id| {
            body.block(id)
                .operations()
                .iter()
                .filter(|op| op.kind == OperationKind::CheckCallDepth)
                .count()
        })
        .sum::<usize>();
    if checks == 0 {
        return None;
    }
    let mut proof = AcyclicCalls {
        env,
        callees,
        known: FxHashMap::default(),
        remaining: budget::CALL_DEPTH_PROOF_WORK,
    };
    if proof.body(body, 0) {
        let mut edit = FunctionEdit::new(body.clone());
        for id in body.blocks() {
            edit.block_mut(id)
                .operations
                .retain(|op| op.kind != OperationKind::CheckCallDepth);
        }
        return Some(edit.finish(env));
    }
    if checks < 2 {
        return None;
    }
    remove_dominated_checks(body, env)
}

/// A bounded proof over immutable callee bodies. A visiting node is recorded as false so a
/// cycle cannot prove itself. Exhausting either budget only keeps an unnecessary check.
/// Unfinished functions and specializations may still have unoptimized bodies. Using them
/// relies on later rewrites not introducing script calls outside their transitive call graph:
/// inlining exposes existing calls, and devirtualization resolves dispatch this proof rejects.
/// Any rewrite that introduces new call paths must preserve or re-establish this guarantee.
struct AcyclicCalls<'a> {
    env: ModuleEnv<'a>,
    callees: SemanticCallees<'a>,
    known: FxHashMap<FunctionId, bool>,
    remaining: usize,
}

impl AcyclicCalls<'_> {
    fn callee(&mut self, id: FunctionId, depth: usize) -> bool {
        if let Some(&known) = self.known.get(&id) {
            return known;
        }
        if depth >= budget::CALL_DEPTH_PROOF_DEPTH || self.remaining == 0 {
            return false;
        }
        self.remaining -= 1;
        self.known.insert(id, false);
        let native = self
            .env
            .module_by_id(id.module)
            .and_then(|module| module.get_function_by_id(id.function))
            .is_some_and(|function| function.code.native_entry().is_some());
        let proven = native
            || self
                .callees
                .body(id)
                .is_some_and(|body| self.body(body, depth + 1));
        self.known.insert(id, proven);
        proven
    }

    fn body(&mut self, body: &Function, depth: usize) -> bool {
        for id in body.blocks() {
            if self.remaining == 0 {
                return false;
            }
            self.remaining -= 1;
            let block = body.block(id);
            if matches!(block.terminator().kind, TerminatorKind::Yield { .. }) {
                return false;
            }
            let invoke = match &block.terminator().kind {
                TerminatorKind::Invoke { operation, .. } => Some(operation),
                _ => None,
            };
            for operation in block.operations().iter().chain(invoke) {
                if self.remaining == 0 {
                    return false;
                }
                self.remaining -= 1;
                if !operation_calls_only(operation, |id| self.callee(id, depth)) {
                    return false;
                }
            }
        }
        true
    }
}

fn remove_dominated_checks(body: &Function, env: ModuleEnv<'_>) -> Option<Function> {
    // A scoped accessor holds an extra frame between project and end_project; a yielding body
    // can resume at a different depth. Neither obeys the constant-depth premise below.
    for id in body.blocks() {
        let block = body.block(id);
        if matches!(block.terminator().kind, TerminatorKind::Yield { .. }) {
            return None;
        }
        let invoke = match &block.terminator().kind {
            TerminatorKind::Invoke { operation, .. } => Some(operation),
            _ => None,
        };
        if block.operations().iter().chain(invoke).any(|op| {
            matches!(
                op.kind,
                OperationKind::Project { .. } | OperationKind::EndProject
            )
        }) {
            return None;
        }
    }
    let successors = body
        .blocks()
        .map(|id| {
            body.block(id)
                .terminator()
                .successors()
                .map(|id| id.as_index())
                .collect()
        })
        .collect::<Vec<Vec<usize>>>();
    let dominance = Dominance::of(&successors, body.entry().as_index());
    let mut edit = FunctionEdit::new(body.clone());
    let mut changed = false;
    let mut pending = vec![(body.entry().as_index(), false)];
    while let Some((index, mut checked)) = pending.pop() {
        let id = BlockId::from_index(index);
        edit.block_mut(id).operations.retain(|op| {
            if op.kind != OperationKind::CheckCallDepth {
                return true;
            }
            // Ordinary calls restore the caller's depth on both normal and error returns.
            // Keep the first check, including its span, and remove only dominated copies.
            let redundant = checked;
            checked = true;
            changed |= redundant;
            !redundant
        });
        pending.extend(
            dominance
                .children(index)
                .iter()
                .map(|&child| (child, checked)),
        );
    }
    changed.then(|| edit.finish(env))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        CompilerSession, Location, MirOptimization,
        hir::function::ArgConvention,
        mir::{Operation, ParameterKind, Value, builder::FunctionBuilder, terminator::Terminator},
        types::r#type::Type,
    };

    fn count(body: &Function) -> usize {
        body.blocks()
            .map(|id| {
                body.block(id)
                    .operations()
                    .iter()
                    .filter(|op| op.kind == OperationKind::CheckCallDepth)
                    .count()
            })
            .sum()
    }

    #[test]
    fn checks_only_disappear_when_an_earlier_check_dominates() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        for guarded_entry in [false, true] {
            let mut builder = FunctionBuilder::new("checks".into(), Default::default());
            let flag = builder.add_parameter(
                Type::primitive::<bool>(),
                ParameterKind::Parameter(ArgConvention::Let),
            );
            let entry = builder.add_block();
            let flag = builder
                .append_operation(entry, Operation::load(span, Value::Parameter(flag)))
                .unwrap();
            let left = builder.add_block();
            let right = builder.add_block();
            let join = builder.add_block();
            if guarded_entry {
                builder.append_operation(entry, Operation::check_call_depth(span));
            }
            builder.set_terminator(entry, Terminator::cond_br(span, flag.clone(), left, right));
            builder.append_operation(left, Operation::check_call_depth(span));
            builder.append_operation(left, Operation::check_call_depth(span));
            builder.set_terminator(left, Terminator::goto(span, join));
            builder.set_terminator(right, Terminator::goto(span, join));
            builder.append_operation(join, Operation::check_call_depth(span));
            builder.append_operation(join, Operation::check_fuel(span));
            // Repeated loop iterations stay at the same frame depth too.
            builder.set_terminator(join, Terminator::cond_br(span, flag.clone(), join, right));
            let body = builder.finish(env);
            let simplified = remove_dominated_checks(&body, env).unwrap();
            assert_eq!(count(&simplified), if guarded_entry { 1 } else { 2 });
            if !guarded_entry {
                assert!(matches!(
                    simplified.block(join).operations()[0].kind,
                    OperationKind::CheckCallDepth
                ));
            }
        }
    }

    #[test]
    fn suspended_frames_prevent_check_deduplication() {
        use crate::{
            ExecutionTarget,
            module::{LocalFunctionId, Path},
        };
        let mut session = CompilerSession::new();
        session.set_allow_experimental(true);
        session.set_mir_optimization(MirOptimization::Disabled);
        let output = session
            .compile_for(
                ExecutionTarget::Mir,
                r#"
            subscript slot(value: &mut int) -> int {
                ref mut { let mut local = value; yield local; value = local; }
            }
            fn main(value: &mut int) { value->[slot] += 1; }
        "#,
                "scoped",
                Path::single_str("scoped"),
            )
            .unwrap();
        let module = session.expect_fresh_module(output.module_id);
        let env = ModuleEnv::new(module, session.raw_modules());
        let artifacts = session
            .mir_artifacts_for(output.module_id, MirOptimization::Disabled)
            .unwrap();
        let mut saw_project = false;
        let mut saw_yield = false;
        for index in 0..module.function_count() {
            let Some(body) = artifacts.get(LocalFunctionId::from_index(index)) else {
                continue;
            };
            let yields = body.blocks().any(|id| {
                matches!(
                    body.block(id).terminator().kind,
                    TerminatorKind::Yield { .. }
                )
            });
            let projects = body.blocks().any(|id| {
                body.block(id)
                    .operations()
                    .iter()
                    .any(|op| matches!(op.kind, OperationKind::Project { .. }))
            });
            if !yields && !projects {
                continue;
            }
            saw_project |= projects;
            saw_yield |= yields;
            let mut edit = FunctionEdit::new(body.clone());
            let span = Location::new_synthesized();
            edit.block_mut(body.entry()).operations.splice(
                0..0,
                [
                    Operation::check_call_depth(span),
                    Operation::check_call_depth(span),
                ],
            );
            let guarded = edit.finish(env);
            assert!(remove_dominated_checks(&guarded, env).is_none());
        }
        assert!(saw_project && saw_yield);
    }

    fn optimized_body(source: &str, name: &str) -> String {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let text = session.emit_mir("checks", source);
        text.split(&format!("fn {name}("))
            .nth(1)
            .unwrap()
            .split("\nfn ")
            .next()
            .unwrap()
            .to_owned()
    }

    #[test]
    fn acyclic_script_helpers_do_not_keep_a_guard() {
        let body = optimized_body(
            r#"
            #[inline(never)] fn leaf(x: int) -> int { x + 1 }
            #[inline(never)] fn helper(x: int) -> int { leaf(x) }
            trait Apply<Self> { fn go(x: Self) -> int; }
            impl Apply for int { fn go(x: int) -> int { helper(x) } }
            fn apply<T>(x: T) -> int where T: Apply { go(x) }
            fn main(x: int) -> int { apply(x) }
        "#,
            "main",
        );
        assert!(body.contains("call checks::helper"), "{body}");
        assert!(!body.contains("check_call_depth"), "{body}");
    }

    #[test]
    fn recursive_and_unknown_callees_keep_a_guard() {
        for source in [
            "fn main(f: (int) -> int, x: int) -> int { f(x) }",
            "fn recurse(x: int) -> int { recurse(x) } trait Apply<Self> { fn go(x: Self) -> int; } impl Apply for int { fn go(x: int) -> int { recurse(x) } } fn apply<T>(x: T) -> int where T: Apply { go(x) } fn main(x: int) -> int { apply(x) }",
        ] {
            let body = optimized_body(source, "main");
            assert!(body.contains("check_call_depth"), "{body}");
        }
    }
}
