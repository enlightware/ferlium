// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Borrowing instead of cloning a read-only local lifetime.
//!
//! Clone/drop pairs have no observable behavior under the language's ownership contract. Their
//! storage can nevertheless be shared only while the source stays alive and unchanged. This pass
//! proves that interval on every success and failure path, stopping at the clone's cleanup drop.
//! Product/variant projections keep their storage root; immutable non-escaping call arguments are
//! readers, whereas mutable/owned arguments, escapes and initialization queries are not.
//!
//! The first version requires a fresh destination with one static clone constructor, and a source
//! rooted in an immutable parameter or a private local allocated before the destination in the
//! same block. It rejects stack restores and CFG cycles inside the borrowed lifetime. These are
//! proof boundaries, not assumptions about lowering. Uses are indexed once, and only candidate
//! lifetime regions are walked; unchanged bodies are never opened for editing.

use std::cell::OnceCell;

use rustc_hash::{FxHashMap, FxHashSet};

use super::{
    dataflow::{Root, call_operands},
    site::OperationSite,
};
use crate::{
    hir::function::ArgConvention,
    mir::{
        self, Function, Operation, OperationKind, ParameterKind, ValueId,
        dominance::Dominance,
        edit::FunctionEdit,
        role::{MirType, ValueRole, ValueRoles},
        site::OperationIndex,
        terminator::TerminatorKind,
    },
    module::id::Id,
};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Access {
    Read,
    Write,
    Escape,
}

#[derive(Clone, Copy)]
struct Use {
    site: OperationSite,
    access: Access,
}

struct Roots<'a> {
    definitions: FxHashMap<ValueId, &'a Operation>,
    resolved: FxHashMap<ValueId, Option<Root>>,
}

impl Roots<'_> {
    fn of(&mut self, value: &mir::Value) -> Option<Root> {
        let &mir::Value::Register(mut id) = value else {
            return match value {
                mir::Value::Parameter(id) => Some(Root::Parameter(*id)),
                _ => None,
            };
        };
        let mut path = Vec::new();
        let found = loop {
            if let Some(root) = self.resolved.get(&id) {
                break *root;
            }
            path.push(id);
            match self.definitions.get(&id) {
                Some(operation) if matches!(operation.kind, OperationKind::Alloca { .. }) => {
                    break Some(Root::Alloca(id));
                }
                Some(operation) if matches!(operation.kind, OperationKind::Subfield { .. }) => {
                    match &operation.operands[0] {
                        mir::Value::Register(base) => id = *base,
                        mir::Value::Parameter(base) => break Some(Root::Parameter(*base)),
                        _ => break None,
                    }
                }
                _ => break None,
            }
        };
        for id in path {
            self.resolved.insert(id, found);
        }
        found
    }
}

/// Returns a rewritten semantic body only after proving an entire borrowed lifetime.
pub(crate) fn borrow_read_only_clones(func: &Function) -> Option<Function> {
    let mut candidates = Vec::new();
    let mut allocas = FxHashMap::default();
    for block in func.blocks() {
        for (index, operation) in func.block(block).operations().iter().enumerate() {
            let site = OperationSite {
                block,
                index: OperationIndex::from_index(index),
            };
            if matches!(operation.kind, OperationKind::Alloca { .. }) {
                allocas.insert(operation.result_id().unwrap(), site);
            } else if matches!(operation.kind, OperationKind::Clone { .. })
                && let mir::Value::Register(destination) = &operation.operands[1]
            {
                candidates.push((site, *destination));
            }
        }
    }
    candidates.retain(|(_, destination)| allocas.contains_key(destination));
    if candidates.is_empty() {
        return None;
    }

    let mut roots = Roots {
        definitions: func
            .blocks()
            .flat_map(|block| {
                let basic = func.block(block);
                basic
                    .operations()
                    .iter()
                    .chain(match &basic.terminator().kind {
                        TerminatorKind::Invoke { operation, .. } => Some(operation),
                        _ => None,
                    })
            })
            .filter_map(|operation| operation.result_id().map(|id| (id, operation)))
            .collect(),
        resolved: FxHashMap::default(),
    };
    let mut tracked = FxHashSet::default();
    candidates.retain(|(site, destination)| {
        let operation = &func.block(site.block).operations()[site.index.as_index()];
        let Some(source) = roots.of(&operation.operands[0]) else {
            return false;
        };
        let eligible_source = match source {
            Root::Parameter(id) => matches!(
                func.parameters()[id.as_index()].kind,
                ParameterKind::Parameter(ArgConvention::Let)
            ),
            Root::Alloca(id) => allocas.get(&id).is_some_and(|source| {
                let destination = allocas[destination];
                source.block == destination.block
                    && source.index.as_u32() < destination.index.as_u32()
            }),
            _ => false,
        };
        if !eligible_source {
            return false;
        }
        tracked.extend([source, Root::Alloca(*destination)]);
        true
    });
    if candidates.is_empty() {
        return None;
    }
    let roles = ValueRoles::derive(func);
    let mut uses: FxHashMap<Root, Vec<Use>> =
        tracked.iter().map(|root| (*root, Vec::new())).collect();
    for block in func.blocks() {
        let basic = func.block(block);
        for (index, operation) in basic
            .operations()
            .iter()
            .chain(match &basic.terminator().kind {
                TerminatorKind::Invoke { operation, .. } => Some(operation),
                _ => None,
            })
            .enumerate()
        {
            let site = OperationSite {
                block,
                index: OperationIndex::from_index(index),
            };
            for (position, operand) in operation.operands.iter().enumerate() {
                if let Some(root) = roots.of(operand)
                    && let Some(uses) = uses.get_mut(&root)
                {
                    uses.push(Use {
                        site,
                        access: access(operation, position, &roles, func),
                    });
                }
            }
        }
        if !matches!(basic.terminator().kind, TerminatorKind::Invoke { .. }) {
            for operand in basic.terminator().operands() {
                if let Some(root) = roots.of(operand)
                    && let Some(uses) = uses.get_mut(&root)
                {
                    uses.push(Use {
                        site: OperationSite {
                            block,
                            index: OperationIndex::from_index(basic.operations().len()),
                        },
                        access: Access::Escape,
                    });
                }
            }
        }
    }

    let dominance = OnceCell::new();
    let mut replacements = FxHashMap::default();
    let mut removed = FxHashSet::default();
    for (site, destination) in candidates {
        let operation = &func.block(site.block).operations()[site.index.as_index()];
        let source = roots.of(&operation.operands[0]).unwrap();
        let destination_uses = &uses[&Root::Alloca(destination)];
        // All source aliases must remain known: even an earlier escape could permit mutation
        // through an unrelated operand during the lifetime being borrowed.
        if uses[&source]
            .iter()
            .any(|usage| usage.access == Access::Escape)
            || destination_uses
                .iter()
                .any(|usage| usage.access == Access::Escape)
        {
            continue;
        }
        let Some(drops) = lifetime(func, site, destination, source, &uses) else {
            continue;
        };
        // A structural source register may have been defined only on the constructor's path.
        // Reachability from that constructor alone does not prove dominance: deriving an unused
        // field address or dropping absent storage can also be legal on a bypass path.
        // The source is available at the clone in valid input MIR. Requiring the clone's block
        // to dominate every retained destination use makes its substitution valid as well.
        if matches!(operation.operands[0], mir::Value::Register(_)) {
            let dominance = dominance.get_or_init(|| {
                let successors = func
                    .blocks()
                    .map(|block| {
                        func.block(block)
                            .terminator()
                            .successors()
                            .map(|target| target.as_index())
                            .collect()
                    })
                    .collect::<Vec<_>>();
                Dominance::of(&successors, func.entry().as_index())
            });
            let cleanup: FxHashSet<_> = drops.iter().copied().collect();
            if destination_uses.iter().any(|usage| {
                usage.site != site
                    && !cleanup.contains(&usage.site)
                    && !dominance.dominates(site.block.as_index(), usage.site.block.as_index())
            }) {
                continue;
            }
        }
        replacements.insert(destination, operation.operands[0].clone());
        removed.insert(site);
        removed.extend(drops);
    }
    if replacements.is_empty() {
        return None;
    }
    // Resolve nested borrowed clones before substitution. Every edge refers to storage already
    // available at the clone, so the replacement graph is acyclic.
    for id in replacements.keys().copied().collect::<Vec<_>>() {
        let mut value = replacements[&id].clone();
        while let mir::Value::Register(source) = &value {
            let Some(next) = replacements.get(source) else {
                break;
            };
            value = next.clone();
        }
        replacements.insert(id, value);
    }
    let mut edit = FunctionEdit::new(func.clone());
    edit.visit_operands_mut(|value| {
        if let mir::Value::Register(id) = value
            && let Some(source) = replacements.get(id)
        {
            *value = source.clone();
        }
    });
    for block in func.blocks() {
        let mut index = 0;
        edit.block_mut(block).operations.retain(|_| {
            let keep = !removed.contains(&OperationSite {
                block,
                index: OperationIndex::from_index(index),
            });
            index += 1;
            keep
        });
    }
    Some(edit.finish_unverified())
}

fn access(operation: &Operation, position: usize, roles: &ValueRoles, func: &Function) -> Access {
    match &operation.kind {
        OperationKind::Subfield { .. } if position == 0 => Access::Read,
        OperationKind::Load if position == 0 => {
            match roles
                .get(
                    &mir::Value::Register(operation.result_id().unwrap()),
                    func.constants(),
                )
                .as_deref()
            {
                Some(ValueRole::Materialized(MirType::Lowered(_))) => Access::Read,
                _ => Access::Escape,
            }
        }
        OperationKind::CompareEqual
        | OperationKind::ExtractTag
        | OperationKind::ExtractPayloadIndirection
            if position == 0 =>
        {
            Access::Read
        }
        OperationKind::Clone { .. } | OperationKind::Memcpy => match position {
            0 => Access::Read,
            1 => Access::Write,
            _ => Access::Escape,
        },
        OperationKind::Store if position == 1 => Access::Write,
        OperationKind::Drop { .. }
        | OperationKind::DropInitialized { .. }
        | OperationKind::Clear
            if position == 0 =>
        {
            Access::Write
        }
        OperationKind::Call { ty, metadata } => {
            let Some(call) = call_operands(&operation.operands, ty) else {
                return Access::Escape;
            };
            if ty.result_convention.returns_borrow() {
                return Access::Escape;
            }
            let start = 1 + call.extras.len();
            if let Some(index) = position.checked_sub(start)
                && let Some((_, convention)) = call.arguments.get(index)
            {
                if metadata
                    .as_deref()
                    .is_some_and(|metadata| metadata.owned_arguments.contains(index))
                {
                    Access::Write
                } else if *convention == ArgConvention::Let {
                    Access::Read
                } else {
                    Access::Write
                }
            } else if operation.operands.get(position) == Some(call.result) {
                Access::Write
            } else {
                Access::Escape
            }
        }
        _ => Access::Escape,
    }
}

/// Proves that every path ends this particular clone lifetime before touching its source.
/// Cycles are rejected explicitly rather than treating a visited node as a completed proof.
fn lifetime(
    func: &Function,
    clone: OperationSite,
    destination: ValueId,
    source: Root,
    uses: &FxHashMap<Root, Vec<Use>>,
) -> Option<Vec<OperationSite>> {
    let destination_uses = &uses[&Root::Alloca(destination)];
    let writes: FxHashSet<_> = uses[&source]
        .iter()
        .chain(destination_uses)
        .filter(|usage| usage.access != Access::Read)
        .map(|usage| usage.site)
        .collect();
    let mut done = FxHashSet::default();
    let mut active = FxHashSet::default();
    let mut visited = FxHashMap::default();
    let OperationKind::Clone { ty: cloned } =
        func.block(clone.block).operations()[clone.index.as_index()].kind
    else {
        unreachable!("candidate is a clone")
    };
    let mut drops = Vec::new();
    let mut work = vec![(clone.block, clone.index.as_index() + 1, false)];
    while let Some((block, start, exiting)) = work.pop() {
        if exiting {
            active.remove(&block);
            done.insert(block);
            continue;
        }
        if active.contains(&block) {
            return None;
        }
        if done.contains(&block) {
            continue;
        }
        active.insert(block);
        work.push((block, start, true));
        let basic = func.block(block);
        let mut ended = false;
        for (index, operation) in basic
            .operations()
            .iter()
            .chain(match &basic.terminator().kind {
                TerminatorKind::Invoke { operation, .. } => Some(operation),
                _ => None,
            })
            .enumerate()
            .skip(start)
        {
            let site = OperationSite {
                block,
                index: OperationIndex::from_index(index),
            };
            if matches!(operation.kind, OperationKind::Drop { ty } if ty == cloned)
                && operation.operands[0] == mir::Value::Register(destination)
            {
                drops.push(site);
                visited.insert(block, (start, index + 1));
                ended = true;
                break;
            }
            if matches!(operation.kind, OperationKind::StackRestore) || writes.contains(&site) {
                return None;
            }
            visited.insert(block, (start, index + 1));
        }
        if !ended {
            let successors: Vec<_> = basic.terminator().successors().collect();
            if successors.is_empty() {
                return None;
            }
            for target in successors {
                work.push((target, 0, false));
            }
        }
    }
    if destination_uses.iter().any(|usage| {
        usage.site != clone
            && !visited
                .get(&usage.site.block)
                .is_some_and(|&(start, end)| (start..end).contains(&usage.site.index.as_index()))
    }) {
        return None;
    }
    Some(drops)
}

#[cfg(test)]
mod tests {
    use super::borrow_read_only_clones;
    use crate::{
        CompilerSession, ExecutionTarget, MirOptimization, Path,
        format::FormatWith,
        mir::{Function, OperationKind, verify::verify_function},
    };
    use ustr::ustr;

    fn check(source: &str, expected: bool) {
        let mut session = CompilerSession::new();
        let module_id = session
            .compile_for(
                ExecutionTarget::Mir,
                source,
                "borrow_clone",
                Path::single_str("borrow_clone"),
            )
            .unwrap()
            .module_id;
        let module = session.expect_fresh_module(module_id);
        let id = module.get_local_function_id(ustr("view")).unwrap();
        let body = session
            .mir_artifacts_for(module_id, MirOptimization::Disabled)
            .unwrap()
            .get(id)
            .unwrap();
        let env = session.modules().env_for(module);
        assert!(
            body.blocks()
                .flat_map(|block| body.block(block).operations())
                .any(|op| matches!(op.kind, OperationKind::Clone { .. })),
            "fixture needs a clone"
        );
        let rewritten = borrow_read_only_clones(body);
        assert_eq!(rewritten.is_some(), expected, "{}", body.format_with(&env));
        if let Some(body) = rewritten {
            verify_function(&body, env);
            assert_eq!(clones(&body), 0, "{}", body.format_with(&env));
        }
    }

    fn clones(body: &Function) -> usize {
        body.blocks()
            .flat_map(|block| body.block(block).operations())
            .filter(|op| matches!(op.kind, OperationKind::Clone { .. }))
            .count()
    }

    #[test]
    fn borrows_immutable_parameter_and_nested_fields() {
        check(
            "fn view(x: string) -> int { let mut copy = x; len(copy) }",
            true,
        );
        check(
            "fn view(x: (string, int)) -> int { let mut copy = x; len(copy.0) + copy.1 }",
            true,
        );
        check(
            "fn view(x: ((string, int), int)) -> int { let mut copy = x; len(copy.0.0) + copy.1 }",
            true,
        );
    }

    #[test]
    fn borrows_nested_local_clone_lifetimes() {
        check(
            "fn view(x: string) -> int { let mut original = x; let mut copy = original; len(copy) }",
            true,
        );
    }

    #[test]
    fn borrows_through_success_and_failure_cleanup() {
        check(
            "fn view(x: string, d: int) -> int { let mut copy = x; idiv(len(copy), d) }",
            true,
        );
    }

    #[test]
    fn rejects_mutation_and_ownership_transfer() {
        check(
            "fn view(x: string) -> int { let mut copy = x; string_push_str(copy, x); len(copy) }",
            false,
        );
        check(
            "fn view(x: string) -> string { let mut copy = x; copy }",
            false,
        );
        check(
            "fn view(x: &mut string) -> int { let mut copy = x; len(copy) }",
            false,
        );
        check(
            "fn view(x: string) -> int { let mut original = x; let mut copy = original; string_push_str(original, x); len(copy) }",
            false,
        );
    }

    #[test]
    fn rejects_a_source_dropped_before_the_borrowed_cleanup() {
        use crate::mir::edit::FunctionEdit;
        let mut session = CompilerSession::new();
        let module_id = session.compile_for(ExecutionTarget::Mir,
            "fn view() -> int { let mut original = to_string(123); let mut copy = original; len(copy) }",
            "early_drop", Path::single_str("early_drop")).unwrap().module_id;
        let module = session.expect_fresh_module(module_id);
        let id = module.get_local_function_id(ustr("view")).unwrap();
        let body = session
            .mir_artifacts_for(module_id, MirOptimization::Disabled)
            .unwrap()
            .get(id)
            .unwrap();
        let env = session.modules().env_for(module);
        assert_eq!(clones(body), 1);
        assert!(
            borrow_read_only_clones(body).is_some(),
            "fixture must otherwise qualify"
        );
        let block = body.blocks().next().unwrap();
        let operations = body.block(block).operations();
        let clone = operations
            .iter()
            .position(|op| matches!(op.kind, OperationKind::Clone { .. }))
            .unwrap();
        let source = &operations[clone].operands[0];
        let drop = operations
            .iter()
            .position(|op| {
                matches!(op.kind, OperationKind::Drop { .. }) && &op.operands[0] == source
            })
            .unwrap();
        assert!(drop > clone);
        let mut edit = FunctionEdit::new(body.clone());
        let operations = &mut edit.block_mut(block).operations;
        let drop = operations.remove(drop);
        operations.insert(clone + 1, drop);
        let body = edit.finish_unverified();
        verify_function(&body, env);
        assert!(borrow_read_only_clones(&body).is_none());
    }

    #[test]
    fn rejects_cycles_and_escaping_accessors() {
        check(
            "fn view(x: string, n: int) -> int { let mut copy = x; let mut total = 0; for i in 0..n { total += len(copy); }; total }",
            false,
        );
        check(
            "fn view(x: [int]) -> int { let mut copy = x; copy[0] }",
            false,
        );
    }
}
