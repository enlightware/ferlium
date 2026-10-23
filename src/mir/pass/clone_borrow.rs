// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Borrowing instead of cloning a read-only local lifetime.
//!
//! Clone/drop pairs have no observable behavior under the language's ownership contract. Their
//! storage can nevertheless be shared only while the source stays alive and unchanged. This pass
//! proves that interval on every success and failure path, stopping at the clone's cleanup drop.
//! Product/variant projections and proven caller-rooted addressors keep their storage root;
//! immutable non-escaping call arguments are readers. Repeatable addressors read their owner;
//! uses of the returned place retain that owner. Other mutable/owned arguments, escapes and
//! initialization queries are not readers.
//!
//! The proof requires a fresh destination with one static clone constructor, and a source
//! rooted in an immutable parameter or a private local allocated before the destination in the
//! same block. A field of a local product is a destination once the product is split into one
//! local per field. Whole moves may carry the copy into further private locals, each initialized
//! only by such a move. A finite-state walk proves read-only lifetimes even across CFG cycles. Stack
//! restores must preserve the source allocation; suspension remains a proof boundary. Uses are
//! indexed once, and unchanged bodies are never opened for editing.
//! Each candidate walks the reachable CFG in at most one state per block and holding local, plus
//! the absent state, including paths before its clone, so proof cost is O(candidates × holders ×
//! reachable blocks and operations). Borrowing repeats while it removes clones.

use std::{cell::OnceCell, collections::hash_map::Entry, iter::once};

use rustc_hash::{FxHashMap, FxHashSet};

use super::{
    dataflow::{CallOperands, Root, call_operands},
    provenance::{AddressorSummary, PlaceOrigins, ResultProvenance},
    site::OperationSite,
    stack_region,
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
    module::{FunctionId, id::Id},
};

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Access {
    Read,
    /// A non-mutating reader whose signature nevertheless requires mutable storage.
    ReadMutable,
    Write,
    Escape,
}

/// The private locals that may hold one clone's copy, in discovery order: the clone's destination
/// first, then the locals whole moves carry it into. Indexed for constant-time membership.
struct Holders {
    ids: Vec<ValueId>,
    index: FxHashMap<ValueId, usize>,
}

impl Holders {
    fn new(destination: ValueId) -> Self {
        Self {
            ids: vec![destination],
            index: FxHashMap::from_iter([(destination, 0)]),
        }
    }

    fn insert(&mut self, id: ValueId) {
        if let Entry::Vacant(entry) = self.index.entry(id) {
            entry.insert(self.ids.len());
            self.ids.push(id);
        }
    }

    fn index_of(&self, id: ValueId) -> Option<usize> {
        self.index.get(&id).copied()
    }
}

#[derive(Clone, Copy)]
struct Use {
    site: OperationSite,
    access: Access,
}

/// Returns a rewritten semantic body only after proving an entire borrowed lifetime.
///
/// Borrowing a clone can make it the source of another: once a local copy of a collection reads
/// its parameter, an element cloned out of that copy is rooted in the parameter too. Repeat until
/// no clone is borrowed; every round removes at least one clone.
pub(crate) fn borrow_read_only_clones(
    func: &Function,
    summary_of: &dyn Fn(FunctionId) -> AddressorSummary,
) -> Option<Function> {
    let mut current = borrow_once(func, summary_of)?;
    while let Some(next) = borrow_once(&current, summary_of) {
        current = next;
    }
    Some(current)
}

fn borrow_once(
    func: &Function,
    summary_of: &dyn Fn(FunctionId) -> AddressorSummary,
) -> Option<Function> {
    let mut candidates = Vec::new();
    let mut allocas = FxHashMap::default();
    let mut moves: FxHashMap<ValueId, Vec<(OperationSite, ValueId)>> = FxHashMap::default();
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
            } else if operation.kind == OperationKind::Move
                && let [mir::Value::Register(from), mir::Value::Register(to)] = &*operation.operands
            {
                moves.entry(*from).or_default().push((site, *to));
            }
        }
    }
    candidates.retain(|(_, destination)| allocas.contains_key(destination));
    if candidates.is_empty() {
        return None;
    }

    let origins = PlaceOrigins::of(func, summary_of);
    let mut tracked = FxHashSet::default();
    candidates.retain(|(site, destination)| {
        let operation = &func.block(site.block).operations()[site.index.as_index()];
        let Some(source) = origins
            .origin_of(&operation.operands[0])
            .map(|origin| origin.root)
        else {
            return false;
        };
        let eligible_source = match source {
            Root::Parameter(id) => matches!(
                func.parameters()[id.as_index()].kind,
                ParameterKind::Place(ArgConvention::Let)
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
        tracked.insert(source);
        true
    });
    // Whole moves between private locals may carry the copy onward. The lifetime proof decides
    // whether each such move really transfers it; collecting every reachable local is enough here.
    let candidates = candidates
        .into_iter()
        .map(|(site, destination)| {
            let mut holders = Holders::new(destination);
            let mut index = 0;
            while let Some(&holder) = holders.ids.get(index) {
                index += 1;
                for &(_, to) in moves.get(&holder).into_iter().flatten() {
                    if allocas.contains_key(&to) {
                        holders.insert(to);
                    }
                }
            }
            tracked.extend(holders.ids.iter().map(|&holder| Root::Alloca(holder)));
            (site, holders)
        })
        .collect::<Vec<_>>();
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
                if let Some(root) = origins.origin_of(operand).map(|origin| origin.root)
                    && let Some(uses) = uses.get_mut(&root)
                {
                    uses.push(Use {
                        site,
                        access: access(operation, position, &roles, func, &origins, summary_of),
                    });
                }
            }
        }
        if !matches!(basic.terminator().kind, TerminatorKind::Invoke { .. }) {
            for operand in basic.terminator().operands() {
                if let Some(root) = origins.origin_of(operand).map(|origin| origin.root)
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
    let mut cleanups = Vec::new();
    let mut preserving_restores = FxHashMap::default();
    for (site, holders) in candidates {
        let operation = &func.block(site.block).operations()[site.index.as_index()];
        let source = origins
            .origin_of(&operation.operands[0])
            .map(|origin| origin.root)
            .unwrap();
        let transfers: FxHashMap<_, _> = holders
            .ids
            .iter()
            .enumerate()
            .flat_map(|(from, holder)| {
                let holders = &holders;
                moves
                    .get(holder)
                    .into_iter()
                    .flatten()
                    .filter_map(move |(site, to)| Some((*site, (from, holders.index_of(*to)?))))
            })
            .collect();
        let holder_uses = || {
            holders
                .ids
                .iter()
                .flat_map(|holder| &uses[&Root::Alloca(*holder)])
        };
        // All source aliases must remain known: even an earlier escape could permit mutation
        // through an unrelated operand during the lifetime being borrowed.
        if uses[&source]
            .iter()
            .any(|usage| usage.access == Access::Escape)
            || holder_uses()
                .any(|usage| usage.access == Access::Escape && !transfers.contains_key(&usage.site))
        {
            continue;
        }
        let Some(drops) = lifetime(
            func,
            site,
            &holders,
            &transfers,
            source,
            &uses,
            &mut |restore| match source {
                // Let parameters borrow caller storage in both interpreters and Wasm;
                // restoring this callee's stack region cannot free that storage.
                Root::Parameter(_) => true,
                Root::Alloca(id) => preserving_restores
                    .entry(id)
                    .or_insert_with(|| stack_region::restores_preserving_alloca(func, id))
                    .contains(&restore),
                _ => false,
            },
        ) else {
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
            if holder_uses().any(|usage| {
                usage.site != site
                    && !cleanup.contains(&usage.site)
                    && !dominance.dominates(site.block.as_index(), usage.site.block.as_index())
            }) {
                continue;
            }
        }
        for &holder in &holders.ids {
            replacements.insert(holder, operation.operands[0].clone());
        }
        cleanups.push((holders.ids, site, drops));
    }
    // A rooted, repeatable addressor proves non-mutation, not write permission. Addressor
    // referents may be shared native members. Require structural storage for mutable readers,
    // following proposed substitutions too so chained clone elimination cannot bypass this rule.
    // Rejecting all such referents is conservative until summaries carry access permissions.
    let rejected = cleanups
        .iter()
        .filter(|(holders, _, _)| {
            let needs_mutable = holders.iter().any(|holder| {
                uses[&Root::Alloca(*holder)]
                    .iter()
                    .any(|usage| usage.access == Access::ReadMutable)
            });
            needs_mutable
                && !supports_mutable_reader(&replacements[&holders[0]], &origins, &replacements)
        })
        .flat_map(|(holders, _, _)| holders.clone())
        .collect::<Vec<_>>();
    for holder in rejected {
        replacements.remove(&holder);
    }
    if replacements.is_empty() {
        return None;
    }
    let removed: FxHashSet<_> = cleanups
        .into_iter()
        .filter(|(holders, _, _)| replacements.contains_key(&holders[0]))
        .flat_map(|(_, site, drops)| once(site).chain(drops))
        .collect();
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

fn supports_mutable_reader<'a>(
    mut source: &'a mir::Value,
    origins: &PlaceOrigins,
    replacements: &'a FxHashMap<ValueId, mir::Value>,
) -> bool {
    loop {
        let Some(origin) = origins.origin_of(source) else {
            return false;
        };
        if !origin.structural {
            return false;
        }
        let Root::Alloca(root) = origin.root else {
            return true;
        };
        let Some(replacement) = replacements.get(&root) else {
            return true;
        };
        source = replacement;
    }
}

pub(super) fn access(
    operation: &Operation,
    position: usize,
    roles: &ValueRoles,
    func: &Function,
    origins: &PlaceOrigins,
    summary_of: &dyn Fn(FunctionId) -> AddressorSummary,
) -> Access {
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
        OperationKind::BuildArray { .. } if position + 1 == operation.operands.len() => {
            Access::Write
        }
        OperationKind::Drop { .. }
        | OperationKind::DropInitialized { .. }
        | OperationKind::Clear
            if position == 0 =>
        {
            Access::Write
        }
        OperationKind::Call { ty, metadata, .. } => {
            let Some(call) = call_operands(operation) else {
                return Access::Escape;
            };
            // Repeatability proves even an `&mut` addressor input is not written by this call.
            // The returned place carries its owner, so later writes through it remain writes.
            let rooted_reader = ty.result_convention.returns_borrow();
            if rooted_reader && !is_rooted_repeatable_addressor(&call, origins, summary_of) {
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
                } else if rooted_reader && *convention == ArgConvention::MutableRef {
                    Access::ReadMutable
                } else if rooted_reader || *convention == ArgConvention::Let {
                    Access::Read
                } else {
                    Access::Write
                }
            } else if call.result.is_some() && operation.operands.get(position) == call.result {
                Access::Write
            } else {
                Access::Escape
            }
        }
        _ => Access::Escape,
    }
}

fn is_rooted_repeatable_addressor(
    call: &CallOperands<'_>,
    origins: &PlaceOrigins,
    summary_of: &dyn Fn(FunctionId) -> AddressorSummary,
) -> bool {
    let mir::Value::Function(callee) = call.callee else {
        return false;
    };
    let summary = summary_of(*callee);
    summary.repeatable
        && matches!(summary.provenance, ResultProvenance::Argument(_))
        && call
            .result
            .is_some_and(|result| origins.returned_origin(result).is_some())
}

/// Checks every reachable state of this clone's lifetime: absent, or held by one of `holders`.
/// The clone initializes the first holder; each of `transfers` moves the copy from one holder to
/// another. A read-only cycle needs no termination proof: every finite exit must end the
/// lifetime, and every active operation must preserve the source. Visiting a block in each state
/// prevents a join from hiding uses after cleanup or a backedge from reconstructing an already
/// active destination. Returns the cleanups and transfers to remove.
fn lifetime(
    func: &Function,
    clone: OperationSite,
    holders: &Holders,
    transfers: &FxHashMap<OperationSite, (usize, usize)>,
    source: Root,
    uses: &FxHashMap<Root, Vec<Use>>,
    preserves_storage: &mut impl FnMut(OperationSite) -> bool,
) -> Option<Vec<OperationSite>> {
    let holder_uses = || {
        holders.ids.iter().enumerate().flat_map(|(holder, id)| {
            uses[&Root::Alloca(*id)]
                .iter()
                .map(move |usage| (holder, usage))
        })
    };
    let writes: FxHashSet<_> = uses[&source]
        .iter()
        .chain(holder_uses().map(|(_, usage)| usage))
        .filter(|usage| !matches!(usage.access, Access::Read | Access::ReadMutable))
        .map(|usage| usage.site)
        .collect();
    let mut holder_sites = FxHashMap::<_, Vec<usize>>::default();
    for (holder, usage) in holder_uses() {
        holder_sites.entry(usage.site).or_default().push(holder);
    }
    // State 0 is absent; state `h + 1` means `holders[h]` holds the copy.
    let mut visited = vec![vec![false; holders.ids.len() + 1]; func.blocks().count()];
    let OperationKind::Clone { ty: cloned } =
        func.block(clone.block).operations()[clone.index.as_index()].kind
    else {
        unreachable!("candidate is a clone")
    };
    // Every holder is initialized only by this lifetime, so it is absent whenever it does not hold
    // the copy, and its cleanup is then a no-op.
    let cleanup_of = |operation: &Operation| {
        if !(matches!(operation.kind, OperationKind::Drop { ty } if ty == cloned)
            || operation.kind == OperationKind::Clear)
        {
            return None;
        }
        let mir::Value::Register(id) = operation.operands[0] else {
            return None;
        };
        holders.index_of(id)
    };
    let mut drops = FxHashSet::default();
    let mut work = vec![(func.entry(), 0)];
    while let Some((block, mut state)) = work.pop() {
        if visited[block.as_index()][state] {
            continue;
        }
        visited[block.as_index()][state] = true;
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
            if site == clone {
                if state != 0 {
                    return None;
                }
                state = 1;
                continue;
            }
            if let Some(&(from, to)) = transfers.get(&site) {
                if state != from + 1 {
                    return None;
                }
                drops.insert(site);
                state = to + 1;
                continue;
            }
            if let Some(holder) = cleanup_of(operation) {
                drops.insert(site);
                if state == holder + 1 {
                    state = 0;
                }
                continue;
            }
            if holder_sites
                .get(&site)
                .is_some_and(|used| used.iter().any(|holder| state != holder + 1))
            {
                return None;
            }
            if state != 0
                && (writes.contains(&site)
                    || matches!(operation.kind, OperationKind::Alloca { .. })
                        && operation.result_id().is_some_and(|id| {
                            holders.index_of(id).is_some() || source == Root::Alloca(id)
                        })
                    || matches!(operation.kind, OperationKind::StackRestore)
                        && !preserves_storage(site))
            {
                return None;
            }
        }
        // A suspended frame can permit mutation outside this function. No local read-only
        // proof covers that interval, even when the source is caller-rooted.
        if state != 0 && matches!(basic.terminator().kind, TerminatorKind::Yield { .. }) {
            return None;
        }
        // Abandoning the frame skips the copy's cleanup; the borrowed source is just as unread.
        let mut successors = basic.terminator().successors().peekable();
        if state != 0 && successors.peek().is_none() && !basic.terminator().kind.abandons_frame() {
            return None;
        }
        work.extend(successors.map(|target| (target, state)));
    }
    // Substitution rewrites unreachable blocks too. Keep the original whole-place rule there:
    // empty cleanup is harmless, but other uses could turn a destination initializer into a
    // write to borrowed storage or make the substituted register unavailable.
    for block in func.blocks() {
        if visited[block.as_index()].iter().any(|&state| state) {
            continue;
        }
        for (index, operation) in func.block(block).operations().iter().enumerate() {
            if cleanup_of(operation).is_some() {
                drops.insert(OperationSite {
                    block,
                    index: OperationIndex::from_index(index),
                });
            }
        }
    }
    for (_, usage) in holder_uses() {
        if visited[usage.site.block.as_index()]
            .iter()
            .any(|&state| state)
        {
            continue;
        }
        let operation = func
            .block(usage.site.block)
            .operations()
            .get(usage.site.index.as_index())?;
        cleanup_of(operation)?;
    }
    Some(drops.into_iter().collect())
}

#[cfg(test)]
mod tests {
    use super::{AddressorSummary, FunctionId, borrow_read_only_clones};
    use crate::{
        CompilerSession, ExecutionTarget, MirOptimization, Path,
        format::FormatWith,
        mir::{Function, OperationKind, verify::verify_function},
    };
    use ustr::ustr;

    fn check(source: &str, expected: bool) {
        let mut session = CompilerSession::new();
        session.set_allow_experimental(true);
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
        let summary_of = |callee: FunctionId| {
            session
                .mir_artifacts_for(callee.module, MirOptimization::Disabled)
                .map_or(AddressorSummary::UNKNOWN, |artifacts| {
                    artifacts.addressor_summary(callee.module, callee.function)
                })
        };
        assert!(
            body.blocks()
                .flat_map(|block| body.block(block).operations())
                .any(|op| matches!(op.kind, OperationKind::Clone { .. })),
            "fixture needs a clone"
        );
        let rewritten = borrow_read_only_clones(body, &summary_of);
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
    fn borrows_caller_rooted_indexed_values_through_success_and_failure_cleanup() {
        for value in ["string", "(string, int)"] {
            let reader = if value == "string" {
                "len(copy)"
            } else {
                "len(copy.0) + copy.1"
            };
            let mut session = CompilerSession::new();
            session.set_mir_optimization(MirOptimization::Enabled);
            let source = format!(
                "fn view(x: [{value}], d: int) -> int {{ let mut copy = x[0]; idiv({reader}, d) }}"
            );
            let body = session.emit_mir("indexed_borrow", &source);
            assert!(
                body.contains("buffer_slot::ref_mut"),
                "fixture needs an addressor: {body}"
            );
            assert!(
                !body.contains(&format!("clone {value}"))
                    && !body.contains(&format!("drop {value}")),
                "the indexed copy and both initialized/absent cleanup paths must borrow: {body}"
            );
        }
    }

    #[test]
    fn borrows_an_array_clone_used_only_by_a_repeatable_addressor() {
        check(
            "fn view(x: [int]) -> int { let mut copy = x; copy[0] }",
            true,
        );
    }

    #[test]
    fn keeps_an_indexed_copy_when_its_owner_changes() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let body = session.emit_mir(
            "indexed_write",
            r#"
            fn view(mut x: [string]) -> int {
                let mut copy = x[0]; x[0] = "changed"; len(copy)
            }
        "#,
        );
        assert!(
            body.contains("clone string"),
            "mutation must retain the copy: {body}"
        );
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

    /// An inlined callee whose `effects_unsafe` failure poisons execution leaves the caller's copy
    /// undropped on that path: abandoning the frame reads neither the copy nor its source.
    #[test]
    fn borrows_across_a_poisoning_exit() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        session.set_allow_unsafe(true);
        let body = session.emit_mir(
            "poisoning_borrow",
            "fn at(x: [string], i: int) -> int { effects_unsafe { len(x[i]) } }
            fn view(x: [string], i: int) -> int { let mut copy = x; at(copy, i) + len(copy) }",
        );
        let view = &body[body.find("fn view(").unwrap()..];
        let view = &view[..view[1..].find("\nfn ").map_or(view.len(), |end| end + 1)];
        assert!(
            view.contains("effect_violation"),
            "fixture needs a poisoning exit: {view}"
        );
        assert!(
            !view.contains("clone [string]"),
            "the copy must borrow its parameter: {view}"
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
        let summary_of = |callee: FunctionId| {
            session
                .mir_artifacts_for(callee.module, MirOptimization::Disabled)
                .map_or(AddressorSummary::UNKNOWN, |artifacts| {
                    artifacts.addressor_summary(callee.module, callee.function)
                })
        };
        assert_eq!(clones(body), 1);
        assert!(
            borrow_read_only_clones(body, &summary_of).is_some(),
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
        assert!(borrow_read_only_clones(&body, &summary_of).is_none());
    }

    #[test]
    fn borrows_read_only_loops_with_parameter_and_local_sources() {
        check(
            "fn view(x: string, n: int) -> int { let mut copy = x; let mut total = 0; for i in 0..n { total += len(copy); }; total }",
            true,
        );
        check(
            "fn view(n: int) -> int { let mut original = to_string(123); let mut copy = original; let mut total = 0; for i in 0..n { let s = to_string(i); total += len(copy) + len(s); }; total }",
            true,
        );
        check(
            "fn view(x: string, n: int, d: int) -> int { let mut copy = x; let mut total = 0; for i in 0..n { for j in 0..n { total += idiv(len(copy), d); }; }; total }",
            true,
        );
        check(
            "fn view(x: string, n: int) -> int { let mut total = 0; for i in 0..n { let mut copy = x; total += len(copy); }; total }",
            true,
        );
    }

    #[test]
    fn borrows_a_local_source_across_loop_body_storage_restores() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let body = session.emit_mir(
            "local_loop_borrow",
            "fn view(n: int) -> int { let mut original = to_string(123); let mut copy = original; let mut total = 0; for i in 0..n { let s = to_string(i); total += len(copy) + len(s); }; total }",
        );
        assert!(
            body.contains("stack_restore"),
            "fixture needs a restore: {body}"
        );
        assert!(
            !body.contains("clone string"),
            "the local copy must borrow: {body}"
        );
    }

    fn optimized_body(source: &str) -> String {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let module = session.emit_mir("field_borrow", source);
        let start = module.find("fn view(").expect("fixture defines view");
        let body = &module[start..];
        body[..body[1..].find("\nfn ").map_or(body.len(), |end| end + 1)].to_string()
    }

    #[test]
    fn managed_traversal_copy_counts_do_not_grow_with_payload_size() {
        use crate::{
            hir::value::Value,
            mir::{
                operation::OperationKindDiscriminant as Op, profile::MirInstructionKind as Kind,
            },
        };
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        session.set_physical_mir_optimization(MirOptimization::Enabled);
        for (ty, input) in [
            (
                "[int]",
                "let mut row = []; for j in 0..n { array_append(row, j) }; let mut rows = []; for i in 0..200 { array_append(rows, row) }; rows",
            ),
            (
                "string",
                "let mut row = \"\"; for j in 0..n { string_push_str(row, \"a\") }; let mut rows = []; for i in 0..200 { array_append(rows, row) }; rows",
            ),
        ] {
            let source = format!("fn input(n: int) -> [{ty}] {{ {input} }}
                fn direct(rows: [{ty}]) -> int {{ let mut n = 0; for row in rows {{ n += len(row) }}; n }}
                fn folded(rows: [{ty}]) -> int {{ fold(rows, 0, |n, row| n + len(row)) }}
                fn indexed(rows: [{ty}]) -> int {{ let mut n = 0; for i in 0..len(rows) {{ n += len(rows[i]) }}; n }}");
            let module = session
                .compile(
                    &source,
                    "traversal_profile",
                    Path::single_str("traversal_profile"),
                )
                .unwrap()
                .module_id;
            let entry = |name: &str| {
                session
                    .expect_fresh_module(module)
                    .get_local_function_id(ustr(name))
                    .unwrap()
            };
            let input = entry("input");
            let entries = [entry("direct"), entry("folded"), entry("indexed")];
            for entry in entries {
                for physical in [false, true] {
                    let mut previous = None;
                    for size in [8isize, 128] {
                        // Construct inputs before enabling the traversal counters.
                        let rows = session
                            .run_entry(
                                ExecutionTarget::Mir,
                                module,
                                input,
                                vec![Value::native(size)],
                            )
                            .unwrap();
                        let (result, profile) = if physical {
                            session.run_physical_mir_entry_profiled(module, entry, vec![rows])
                        } else {
                            session.run_mir_entry_profiled(module, entry, vec![rows])
                        }
                        .unwrap();
                        assert_eq!(result.into_primitive_ty::<isize>().unwrap(), 200 * size);
                        for op in [Op::Clone, Op::RuntimeAlloc] {
                            assert_eq!(
                                profile.total().get(Kind::Operation(op)),
                                0,
                                "{ty}, physical={physical}, size={size}, {op:?}"
                            );
                        }
                        let copies = profile.total().get(Kind::Operation(Op::Memcpy));
                        if let Some(previous) = previous {
                            assert_eq!(copies, previous);
                        }
                        previous = Some(copies);
                    }
                }
            }
        }
    }

    #[test]
    fn borrows_managed_iteration_payloads() {
        for ty in ["string", "[int]"] {
            for expression in [
                "let mut n = 0; for row in x { n += len(row) }; n",
                "fold(x, 0, |n, row| n + len(row))",
            ] {
                let body = optimized_body(&format!("fn view(x: [{ty}]) -> int {{ {expression} }}"));
                assert!(
                    !body.contains("clone "),
                    "read-only traversal must borrow all payloads:\n{body}"
                );
            }
        }
    }

    #[test]
    fn borrows_product_iteration_payloads() {
        // The element is cloned into `Some` as a whole product, which must stay one local.
        for (ty, read) in [
            (
                "{ name: string, scores: [int] }",
                "len(p.name) + len(p.scores)",
            ),
            ("([int], int)", "len(p.0) + p.1"),
        ] {
            for expression in [
                format!("let mut n = 0; for p in x {{ n += {read} }}; n"),
                format!("fold(x, 0, |n, p| n + {read})"),
                format!("iter(x) |> filter(|p| {read} > 0) |> map(|p| {read}) |> sum()"),
            ] {
                let body = optimized_body(&format!("fn view(x: [{ty}]) -> int {{ {expression} }}"));
                assert!(
                    !body.contains("clone "),
                    "read-only traversal must borrow product payloads:\n{body}"
                );
            }
        }
    }

    #[test]
    fn borrows_managed_payloads_of_general_local_variants() {
        for source in [
            "fn view(flag: bool, text: string, rows: [int]) -> int { let v = if flag { Text(text) } else { Rows(rows) }; match v { Text(s) => len(s), Rows(r) => len(r) } }",
            "fn view(flag: bool, text: string, rows: [int]) -> int { let v = if flag { Both(text, rows) } else { Neither }; match v { Both(s, r) => len(s) + len(r), _ => 0 } }",
        ] {
            let body = optimized_body(source);
            assert!(
                !body.contains("clone "),
                "managed cases must borrow independently:\n{body}"
            );
        }
    }

    #[test]
    fn borrows_a_clone_into_a_field_of_a_fresh_product() {
        // An inlined array iterator holds a copy of the array it reads; its cursor is trivial.
        for (source, cloned, dropped) in [
            (
                "fn view(x: [int]) -> int { let mut n = 0; for a in x { n += a }; n }",
                "clone [int]",
                "drop ArrayIterator",
            ),
            (
                "fn view(x: [string]) -> int { let mut n = 0; for s in x { n += len(s) }; n }",
                "clone [string]",
                "drop ArrayIterator",
            ),
            (
                "fn view(n: int) -> int { let mut x = [1, 2, n]; let mut s = 0; for a in x { s += a }; s + x[0] }",
                "clone [int]",
                "drop ArrayIterator",
            ),
            (
                "fn view(x: string) -> int { let p = (x, 1); len(p.0) + p.1 }",
                "clone string",
                "drop (string, int)",
            ),
            // Each managed field is split into a local of its own, which borrows independently.
            (
                "fn view(x: string, y: string) -> int { let p = (x, y); len(p.0) + len(p.1) }",
                "clone string",
                "drop (string, string)",
            ),
        ] {
            let body = optimized_body(source);
            assert!(
                !body.contains(cloned) && !body.contains(dropped),
                "the field must borrow its source: {body}"
            );
        }
    }

    #[test]
    fn keeps_a_field_clone_when_its_source_or_product_is_otherwise_observed() {
        for source in [
            // The local source changes while the iterator holds its copy.
            "fn view(n: int) -> int { let mut x = [1, 2, n]; let mut s = 0; for a in x { array_append(x, a); s += a }; s + len(x) }",
            // The whole product escapes.
            "fn view(x: string) -> (string, int) { let p = (x, 1); p }",
        ] {
            let body = optimized_body(source);
            assert!(body.contains("clone "), "the copy must remain: {body}");
        }
    }

    #[test]
    fn retains_loop_clones_when_the_copy_or_local_source_changes() {
        check(
            "fn view(x: string, n: int) -> int { let mut copy = x; for i in 0..n { string_push_str(copy, x); }; len(copy) }",
            false,
        );
        check(
            "fn view(n: int) -> int { let mut original = to_string(123); let mut copy = original; for i in 0..n { string_push_str(original, \"x\"); }; len(copy) }",
            false,
        );
    }

    #[test]
    fn specialized_matrix_multiplication_borrows_its_inputs() {
        let mut session = CompilerSession::new();
        session.set_allow_experimental(true);
        session.set_mir_optimization(MirOptimization::Enabled);
        let source = format!(
            "{}\nfn view(a: Matrix<float>, b: Matrix<float>) -> Matrix<float> {{ matrix_mul(a, b) }}",
            include_str!("../../../tests/modules/linalg.fer")
        );
        let module_id = session
            .compile_for(
                ExecutionTarget::Mir,
                &source,
                "matrix_borrow",
                Path::single_str("matrix_borrow"),
            )
            .unwrap()
            .module_id;
        session.emit_mir_module(module_id);
        let module = session.expect_fresh_module(module_id);
        let original = module.get_local_function_id(ustr("matrix_mul")).unwrap();
        let artifacts = session
            .mir_artifacts_for(module_id, MirOptimization::Enabled)
            .unwrap();
        let bodies = artifacts
            .specializations()
            .iter()
            .filter(|specialization| {
                specialization.original
                    == FunctionId {
                        module: module_id,
                        function: original,
                    }
            })
            .collect::<Vec<_>>();
        assert!(
            !bodies.is_empty(),
            "fixture must specialize matrix multiplication"
        );
        for specialization in bodies {
            // Inputs borrow their sources; the fresh output moves into the returned matrix.
            assert_eq!(
                clones(&specialization.body),
                0,
                "{}",
                specialization
                    .body
                    .format_with(&session.modules().env_for(module))
            );
        }
    }

    #[test]
    fn rejects_scoped_accessors() {
        check(
            "subscript held(value: string) -> string { ref { let mut local = value; yield local } }\n\
             fn view(x: string) -> int { let mut copy = x; len(copy->[held]) }",
            false,
        );
    }
}
