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
//! same block. The destination may also be a static field path into a fresh product whose other
//! fields are `TrivialCopy` and whose drop is structural: that product's drop then ends the
//! lifetime, and the product is otherwise observed only through other fields, as an inlined
//! iterator holding a copy of the array it reads. A finite-state walk proves read-only lifetimes even across CFG cycles. Stack
//! restores must preserve the source allocation; suspension remains a proof boundary. Uses are
//! indexed once, and unchanged bodies are never opened for editing.
//! Each candidate walks the reachable CFG in at most two states per block, including paths
//! before its clone, so proof cost is O(candidates × reachable blocks and operations).

use std::{cell::OnceCell, iter::once};

use rustc_hash::{FxHashMap, FxHashSet};

use super::{
    dataflow::{CallOperands, Root, call_operands, field_index},
    provenance::{AddressorSummary, PlaceOrigins, ResultProvenance},
    scalar_replace::{Parts, parts},
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
    module::{FunctionId, ModuleEnv, id::Id},
    types::{r#type::Type, type_properties::concrete_type_is_trivial_copy},
};

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Access {
    Read,
    /// A non-mutating reader whose signature nevertheless requires mutable storage.
    ReadMutable,
    Write,
    Escape,
}

#[derive(Clone, Copy)]
struct Use {
    site: OperationSite,
    access: Access,
}

/// The storage whose drop ends a clone's lifetime: the destination itself, or the fresh product
/// containing it.
#[derive(Clone, Copy)]
struct Cleanup {
    storage: ValueId,
    ty: Type,
}

/// Returns a rewritten semantic body only after proving an entire borrowed lifetime.
pub(crate) fn borrow_read_only_clones(
    func: &Function,
    env: ModuleEnv<'_>,
    summary_of: &dyn Fn(FunctionId) -> AddressorSummary,
) -> Option<Function> {
    let mut candidates = Vec::new();
    let mut allocas = FxHashMap::default();
    let mut subfields = FxHashMap::default();
    for block in func.blocks() {
        for (index, operation) in func.block(block).operations().iter().enumerate() {
            let site = OperationSite {
                block,
                index: OperationIndex::from_index(index),
            };
            match &operation.kind {
                OperationKind::Alloca { .. } => {
                    allocas.insert(operation.result_id().unwrap(), site);
                }
                OperationKind::Subfield { .. } => {
                    subfields.insert(operation.result_id().unwrap(), operation);
                }
                OperationKind::Clone { .. } => {
                    if let mir::Value::Register(destination) = &operation.operands[1] {
                        candidates.push((site, *destination));
                    }
                }
                _ => {}
            }
        }
    }
    let mut cleanups_of = FxHashMap::default();
    candidates.retain(|(site, destination)| {
        let cleanup = if let Some(site) = allocas.get(destination) {
            let OperationKind::Alloca { ty } =
                func.block(site.block).operations()[site.index.as_index()].kind
            else {
                unreachable!("an alloca site")
            };
            Cleanup {
                storage: *destination,
                ty,
            }
        } else {
            let OperationKind::Clone { ty } =
                func.block(site.block).operations()[site.index.as_index()].kind
            else {
                unreachable!("candidate is a clone")
            };
            let Some(cleanup) =
                product_field_cleanup(func, env, *destination, ty, &allocas, &subfields)
            else {
                return false;
            };
            cleanup
        };
        cleanups_of.insert(*destination, cleanup);
        true
    });
    if candidates.is_empty() {
        return None;
    }

    let field_roots: FxHashSet<_> = cleanups_of
        .iter()
        .filter(|(destination, cleanup)| **destination != cleanup.storage)
        .map(|(destination, _)| *destination)
        .collect();
    let origins = PlaceOrigins::with_field_roots(func, summary_of, field_roots);
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
                ParameterKind::Parameter(ArgConvention::Let)
            ),
            Root::Alloca(id) => allocas.get(&id).is_some_and(|source| {
                let destination = allocas[&cleanups_of[destination].storage];
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
    for (site, destination) in candidates {
        let operation = &func.block(site.block).operations()[site.index.as_index()];
        let source = origins
            .origin_of(&operation.operands[0])
            .map(|origin| origin.root)
            .unwrap();
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
        let Some(drops) = lifetime(
            func,
            site,
            destination,
            cleanups_of[&destination],
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
            if destination_uses.iter().any(|usage| {
                usage.site != site
                    && !cleanup.contains(&usage.site)
                    && !dominance.dominates(site.block.as_index(), usage.site.block.as_index())
            }) {
                continue;
            }
        }
        replacements.insert(destination, operation.operands[0].clone());
        cleanups.push((destination, site, drops));
    }
    // A rooted, repeatable addressor proves non-mutation, not write permission. Addressor
    // referents may be shared native members. Require structural storage for mutable readers,
    // following proposed substitutions too so chained clone elimination cannot bypass this rule.
    // Rejecting all such referents is conservative until summaries carry access permissions.
    let rejected = replacements
        .iter()
        .filter_map(|(&destination, source)| {
            let needs_mutable = uses[&Root::Alloca(destination)]
                .iter()
                .any(|usage| usage.access == Access::ReadMutable);
            (needs_mutable && !supports_mutable_reader(source, &origins, &replacements))
                .then_some(destination)
        })
        .collect::<Vec<_>>();
    for destination in rejected {
        replacements.remove(&destination);
    }
    if replacements.is_empty() {
        return None;
    }
    let removed: FxHashSet<_> = cleanups
        .into_iter()
        .filter(|(destination, _, _)| replacements.contains_key(destination))
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
        OperationKind::Call { ty, metadata } => {
            let Some(call) = call_operands(&operation.operands, ty) else {
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
            } else if operation.operands.get(position) == Some(call.result) {
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
        && origins.returned_origin(call.result).is_some()
}

/// Checks every reachable absent/active state of this clone's lifetime. A read-only cycle needs
/// no termination proof: every finite exit must end the lifetime, and every active operation
/// must preserve the source. Visiting a block in both states prevents a join from hiding uses
/// after cleanup or a backedge from reconstructing an already active destination.
fn lifetime(
    func: &Function,
    clone: OperationSite,
    destination: ValueId,
    cleanup: Cleanup,
    source: Root,
    uses: &FxHashMap<Root, Vec<Use>>,
    preserves_storage: &mut impl FnMut(OperationSite) -> bool,
) -> Option<Vec<OperationSite>> {
    let destination_uses = &uses[&Root::Alloca(destination)];
    let writes: FxHashSet<_> = uses[&source]
        .iter()
        .chain(destination_uses)
        .filter(|usage| !matches!(usage.access, Access::Read | Access::ReadMutable))
        .map(|usage| usage.site)
        .collect();
    let destination_sites: FxHashSet<_> = destination_uses.iter().map(|usage| usage.site).collect();
    let mut visited = vec![[false; 2]; func.blocks().count()];
    let is_cleanup = |operation: &Operation| {
        matches!(operation.kind, OperationKind::Drop { ty } if ty == cleanup.ty)
            && operation.operands[0] == mir::Value::Register(cleanup.storage)
    };
    let mut drops = FxHashSet::default();
    let mut work = vec![(func.entry(), false)];
    while let Some((block, mut active)) = work.pop() {
        if visited[block.as_index()][usize::from(active)] {
            continue;
        }
        visited[block.as_index()][usize::from(active)] = true;
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
                if active {
                    return None;
                }
                active = true;
                continue;
            }
            if is_cleanup(operation) {
                drops.insert(site);
                active = false;
                continue;
            }
            if !active && destination_sites.contains(&site) {
                return None;
            }
            if active
                && (writes.contains(&site)
                    || matches!(operation.kind, OperationKind::Alloca { .. })
                        && operation
                            .result_id()
                            .is_some_and(|id| id == cleanup.storage || source == Root::Alloca(id))
                    || matches!(operation.kind, OperationKind::StackRestore)
                        && !preserves_storage(site))
            {
                return None;
            }
        }
        // A suspended frame can permit mutation outside this function. No local read-only
        // proof covers that interval, even when the source is caller-rooted.
        if active && matches!(basic.terminator().kind, TerminatorKind::Yield { .. }) {
            return None;
        }
        let mut successors = basic.terminator().successors().peekable();
        if active && successors.peek().is_none() {
            return None;
        }
        work.extend(successors.map(|target| (target, active)));
    }
    // Substitution rewrites unreachable blocks too. Keep the original whole-place rule there:
    // empty cleanup is harmless, but other uses could turn a destination initializer into a
    // write to borrowed storage or make the substituted register unavailable.
    for block in func.blocks() {
        if visited[block.as_index()].iter().any(|&state| state) {
            continue;
        }
        for (index, operation) in func.block(block).operations().iter().enumerate() {
            if is_cleanup(operation) {
                drops.insert(OperationSite {
                    block,
                    index: OperationIndex::from_index(index),
                });
            }
        }
    }
    for usage in destination_uses {
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
        if !is_cleanup(operation) {
            return None;
        }
    }
    Some(drops.into_iter().collect())
}

/// The cleanup of a clone into a static field path of a fresh product, when dropping that product
/// drops nothing but the cloned field: every product on the path has a structural drop and
/// `TrivialCopy` other fields, and the path's places are otherwise only projected to other fields.
/// Removing the clone and the product's drop then leaves an absent field that nothing observes.
fn product_field_cleanup(
    func: &Function,
    env: ModuleEnv<'_>,
    destination: ValueId,
    cloned: Type,
    allocas: &FxHashMap<ValueId, OperationSite>,
    subfields: &FxHashMap<ValueId, &Operation>,
) -> Option<Cleanup> {
    // Each place on the path, from the fresh product down, with its field towards the destination
    // and the register projecting that field.
    let mut path = FxHashMap::default();
    let mut current = destination;
    let storage = loop {
        let operation = subfields.get(&current)?;
        let OperationKind::Subfield {
            variant_payload: false,
            ..
        } = operation.kind
        else {
            return None;
        };
        let mir::Value::Register(base) = operation.operands[0] else {
            return None;
        };
        let field = field_index(&operation.operands[1], func)?.as_index();
        if path.insert(base, (field, current)).is_some() {
            return None;
        }
        if allocas.contains_key(&base) {
            break base;
        }
        current = base;
    };
    let site = allocas[&storage];
    let OperationKind::Alloca { ty: storage_ty } =
        func.block(site.block).operations()[site.index.as_index()].kind
    else {
        unreachable!("an alloca site")
    };
    let mut ty = storage_ty;
    let mut place = storage;
    while let Some(&(field, projected)) = path.get(&place) {
        let Parts::Product(fields) = parts(ty, env)? else {
            return None;
        };
        if fields.iter().enumerate().any(|(index, field_ty)| {
            index != field && !concrete_type_is_trivial_copy(*field_ty, &env)
        }) {
            return None;
        }
        ty = *fields.get(field)?;
        place = projected;
    }
    if ty != cloned {
        return None;
    }
    for block in func.blocks() {
        let basic = func.block(block);
        let invoke = match &basic.terminator().kind {
            TerminatorKind::Invoke { operation, .. } => Some(operation),
            _ => None,
        };
        for operation in basic.operations().iter().chain(invoke) {
            for (position, operand) in operation.operands.iter().enumerate() {
                let mir::Value::Register(id) = operand else {
                    continue;
                };
                let Some(&(field, projected)) = path.get(id) else {
                    continue;
                };
                let allowed = match operation.kind {
                    OperationKind::Subfield {
                        variant_payload: false,
                        ..
                    } if position == 0 => {
                        operation.result_id() == Some(projected)
                            || field_index(&operation.operands[1], func)
                                .is_some_and(|other| other.as_index() != field)
                    }
                    OperationKind::Drop { ty } => {
                        *id == storage && position == 0 && ty == storage_ty
                    }
                    _ => false,
                };
                if !allowed {
                    return None;
                }
            }
        }
        if invoke.is_none()
            && basic
                .terminator()
                .operands()
                .iter()
                .any(|operand| matches!(operand, mir::Value::Register(id) if path.contains_key(id)))
        {
            return None;
        }
    }
    Some(Cleanup {
        storage,
        ty: storage_ty,
    })
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
        let rewritten = borrow_read_only_clones(body, env, &summary_of);
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
            borrow_read_only_clones(body, env, &summary_of).is_some(),
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
        assert!(borrow_read_only_clones(&body, env, &summary_of).is_none());
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
            // Dropping the product also drops another managed field.
            "fn view(x: string, y: string) -> int { let p = (x, y); len(p.0) + len(p.1) }",
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
