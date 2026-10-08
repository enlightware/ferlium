// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Hoisting of loop-invariant pure calls and initialized copyable memory reads.
//!
//! An empty effect row excludes source-level effects and failure, while a separate `will_return`
//! proof excludes divergence when the call moves onto a zero-trip path. The pass admits any direct
//! call under those generic contracts with a concrete `TrivialCopy` value result.
//!
//! The first implementation is deliberately narrow but generic over those calls. It recognizes
//! natural loops from dominance backedges, requires one unconditional preheader, and moves a call
//! only when every input place is defined before that preheader and its storage root is unchanged
//! throughout the loop. An input may instead be a [value cell](super::value_cells) whose definition
//! in the loop stores a constant, a bare function or a register defined before the loop, and whose
//! every use stays in the loop: the definition, with any loop-local allocation, moves with the call.
//! The result must be a whole local `alloca`; no other write may reach it and every use of its root
//! must stay in the loop. When that allocation is loop-local it moves with the call.
//!
//! Stack regions are part of correctness, not cleanup decoration. A loop-local result moved after a
//! preheader's `stack_save` would be popped by the matching per-iteration `stack_restore`. The
//! insertion point is therefore before every outside-loop marker restored inside the loop. A marker
//! defined before the preheader leaves no safe insertion point, and the candidate is rejected.
//!
//! Memory reads use the clone-borrowing pass's provenance and access classification. Only static
//! product paths of initialized `Let` parameters or whole locals initialized in the preheader are
//! admitted; rooted writes, escapes and storage invalidation block motion. `Load` moves its value
//! definition; a `Memcpy` into a single-writer copyable local moves with its allocation when needed.
//! Reads are planned together against one analysis and prefer the outermost eligible loop.
//!
//! The pass adds no operation and clones no expression. Acyclic bodies return before candidate
//! scanning. Read candidates must have a syntactically available static product path before roles,
//! provenance or access classification are derived; access indexing covers candidate roots only.

use std::cell::OnceCell;

use rustc_hash::{FxHashMap, FxHashSet};

use super::{
    clone_borrow::{self, Access},
    dataflow::{self, Root},
    local_cells::{self, Allocation, LocalCells},
    loops::{NaturalLoop, cfg, natural_loops},
    provenance::{AddressorSummary, PlaceOrigins},
    site::{OperationIndex, OperationSite},
    stack_region,
    value_cells::{self, Definition, ValueCells},
};
use crate::{
    hir::function::ArgConvention,
    mir::{
        self, BlockId, Function, Operation, OperationKind, ParameterKind,
        dominance::Dominance,
        edit::FunctionEdit,
        role::{MirType, ValueRole, ValueRoles},
        terminator::TerminatorKind,
        value::ValueId,
    },
    module::{FunctionId, ModuleEnv, id::Id},
    types::{
        r#type::{CallResultConvention, Type},
        type_properties::concrete_type_is_trivial_copy,
    },
};

struct LoopAnalysis {
    dominance: Dominance,
    /// Innermost first for calls; reads traverse this in reverse.
    loops: Vec<NaturalLoop>,
}

impl LoopAnalysis {
    fn of(func: &Function) -> Self {
        let (successors, predecessors) = cfg(func);
        let dominance = Dominance::of(&successors, func.entry().as_index());
        let mut loops = natural_loops(func, &successors, &predecessors, &dominance);
        // Canonical MIR requires definitions to precede uses in block-index order as well as
        // dominate them. A moved allocation can be used in any loop block, so the preheader must
        // precede the whole loop. Motion preserves block ids, making this a CFG-only restriction.
        loops.retain(|natural| {
            natural
                .blocks
                .iter()
                .all(|block| natural.preheader.as_index() < block.as_index())
        });
        loops.sort_by_key(|natural| natural.blocks.len());
        Self { dominance, loops }
    }
}

struct LoopStorage {
    restores: Vec<OperationSite>,
    insertion_limit: Option<OperationIndex>,
}

impl LoopStorage {
    fn of(
        func: &Function,
        natural: &NaturalLoop,
        definitions: &FxHashMap<ValueId, OperationSite>,
    ) -> Self {
        let restores: Vec<_> = natural
            .blocks
            .iter()
            .flat_map(|block| {
                func.block(*block)
                    .operations()
                    .iter()
                    .enumerate()
                    .filter_map(|(index, operation)| {
                        matches!(operation.kind, OperationKind::StackRestore).then_some(
                            OperationSite {
                                block: *block,
                                index: OperationIndex::from_index(index),
                            },
                        )
                    })
            })
            .collect();
        let insertion_limit = restores.iter().try_fold(
            func.block(natural.preheader).operations().len(),
            |latest, site| {
                let operation = &func.block(site.block).operations()[site.index.as_index()];
                let mir::Value::Register(marker) = operation.operands[0] else {
                    return None;
                };
                let definition = definitions.get(&marker)?;
                if natural.blocks.contains(&definition.block) {
                    Some(latest)
                } else if definition.block == natural.preheader {
                    Some(latest.min(definition.index.as_index()))
                } else {
                    None
                }
            },
        );
        Self {
            restores,
            insertion_limit: insertion_limit.map(OperationIndex::from_index),
        }
    }
}

#[derive(Clone, Copy)]
struct Alloca {
    site: OperationSite,
    ty: Type,
    is_static: bool,
}

struct Hoist {
    /// The operations to move, in their new order: the definitions of input value cells and the
    /// cells' loop-local allocations, then the call's loop-local result allocation, then the call.
    operations: Vec<OperationSite>,
    preheader: BlockId,
    insertion: OperationIndex,
}

#[derive(Default)]
struct PlaceRoots {
    registers: FxHashMap<ValueId, Root>,
}

impl PlaceRoots {
    fn of(func: &Function) -> Self {
        let mut roots = Self::default();
        for block in func.blocks() {
            for operation in func.block(block).operations() {
                let Some(result) = operation.result_id() else {
                    continue;
                };
                let root = match operation.kind {
                    OperationKind::Alloca { .. }
                    | OperationKind::AllocaPlace { .. }
                    | OperationKind::RuntimeAlloc { .. }
                    | OperationKind::SubscriptMember { .. } => Some(Root::Alloca(result)),
                    OperationKind::DictEntry { .. } => Some(Root::DictEntry(result)),
                    _ => None,
                };
                if let Some(root) = root {
                    roots.registers.insert(result, root);
                }
            }
        }

        // A subfield keeps its base root. Canonical MIR normally orders the definition first; the
        // fixed point also covers bodies whose blocks were edited without being reordered yet.
        loop {
            let mut changed = false;
            for block in func.blocks() {
                for operation in func.block(block).operations() {
                    if !matches!(operation.kind, OperationKind::Subfield { .. }) {
                        continue;
                    }
                    let (Some(result), Some(root)) =
                        (operation.result_id(), roots.root_of(&operation.operands[0]))
                    else {
                        continue;
                    };
                    changed |= roots.registers.insert(result, root) != Some(root);
                }
            }
            if !changed {
                break;
            }
        }
        roots
    }

    fn root_of(&self, value: &mir::Value) -> Option<Root> {
        match value {
            mir::Value::Register(id) => self.registers.get(id).copied(),
            mir::Value::Parameter(id) => Some(Root::Parameter(*id)),
            _ => None,
        }
    }
}

/// Hoists initialized memory reads and calls admitted by LICM, returning `None` when nothing moved.
///
/// Read candidates share one analysis. Calls move one at a time so a call hoisted from an inner
/// loop can move through an enclosing loop on the next iteration. Only operation-dependent facts
/// are rebuilt: motion preserves the CFG, dominance and natural loops. Every successful iteration
/// moves a call across at least one loop boundary, so loop nesting bounds the repeats.
pub(crate) fn hoist_loop_invariants(
    func: &Function,
    env: ModuleEnv<'_>,
    will_return: &impl Fn(FunctionId) -> bool,
    is_optimization_barrier: &impl Fn(FunctionId) -> bool,
    summary_of: &dyn Fn(FunctionId) -> AddressorSummary,
) -> Option<Function> {
    // Every directed cycle has an edge that does not increase an arbitrary total ordering of its
    // vertices. Block ids provide that order, making this an allocation-free rejection of acyclic
    // bodies before the real CFG and dominance analysis.
    let may_have_loop = func.blocks().any(|block| {
        func.block(block)
            .terminator()
            .successors()
            .any(|successor| successor.as_index() <= block.as_index())
    });
    if !may_have_loop {
        return None;
    }
    let mut has_eligible_call = false;
    let mut has_load = false;
    for operation in func
        .blocks()
        .flat_map(|block| func.block(block).operations())
    {
        has_load |= matches!(operation.kind, OperationKind::Load | OperationKind::Memcpy);
        if !has_eligible_call {
            has_eligible_call =
                eligible_call(operation, env, will_return, is_optimization_barrier).is_some();
        }
        if has_load && has_eligible_call {
            break;
        }
    }
    if !has_eligible_call && !has_load {
        return None;
    }

    let analysis = LoopAnalysis::of(func);
    if analysis.loops.is_empty() {
        return None;
    }
    let mut current = has_load
        .then(|| hoist_invariant_loads(func, env, summary_of, &analysis))
        .flatten();
    if !has_eligible_call {
        return current;
    }
    loop {
        let source = current.as_ref().unwrap_or(func);
        let Some(hoist) = find_hoist(source, env, will_return, is_optimization_barrier, &analysis)
        else {
            break;
        };
        current = Some(apply_hoist(source, hoist));
    }
    current
}

/// Move existing copyable reads, their static product projections and any loop-local result storage.
/// Plans share one analysis and prefer the outermost loop that admits each read.
fn hoist_invariant_loads(
    func: &Function,
    env: ModuleEnv<'_>,
    summary_of: &dyn Fn(FunctionId) -> AddressorSummary,
    analysis: &LoopAnalysis,
) -> Option<Function> {
    let dominance = &analysis.dominance;
    let loops = &analysis.loops;
    let (definitions, allocas) = definitions(func);
    let mut candidates: Vec<_> = func
        .blocks()
        .flat_map(|block| {
            func.block(block)
                .operations()
                .iter()
                .enumerate()
                .filter_map(move |(index, operation)| {
                    matches!(operation.kind, OperationKind::Load | OperationKind::Memcpy).then_some(
                        OperationSite {
                            block,
                            index: OperationIndex::from_index(index),
                        },
                    )
                })
        })
        .filter(|site| {
            let source = &func.block(site.block).operations()[site.index.as_index()].operands[0];
            loops.iter().any(|natural| {
                natural.blocks.contains(&site.block)
                    && invariant_place(
                        source,
                        func,
                        &definitions,
                        dominance,
                        natural,
                        &mut Vec::new(),
                    )
            })
        })
        .collect();
    if candidates.is_empty() {
        return None;
    }
    let roles = ValueRoles::derive(func);
    candidates.retain(|site| {
        let operation = &func.block(site.block).operations()[site.index.as_index()];
        let ty = match operation.kind {
            OperationKind::Memcpy => match roles
                .get(&operation.operands[1], func.constants())
                .as_deref()
            {
                Some(ValueRole::Place(MirType::Lowered(ty))) => Some(*ty),
                _ => None,
            },
            OperationKind::Load => match roles
                .get(
                    &mir::Value::Register(operation.result_id().unwrap()),
                    func.constants(),
                )
                .as_deref()
            {
                Some(ValueRole::Materialized(MirType::Lowered(ty))) => Some(*ty),
                _ => None,
            },
            _ => unreachable!(),
        };
        ty.is_some_and(|ty| concrete_type_is_trivial_copy(ty, &env))
    });
    if candidates.is_empty() {
        return None;
    }
    let origins = PlaceOrigins::of(func, summary_of);
    let roots = OnceCell::new();
    let tracked: FxHashSet<_> = candidates
        .iter()
        .flat_map(|site| {
            let operation = &func.block(site.block).operations()[site.index.as_index()];
            operation
                .operands
                .iter()
                .filter_map(|operand| origins.origin_of(operand).map(|origin| origin.root))
        })
        .collect();
    let mut escaped = FxHashSet::default();
    let mut writes: FxHashMap<Root, Vec<OperationSite>> = FxHashMap::default();
    let mut uses: FxHashMap<Root, FxHashSet<BlockId>> = FxHashMap::default();
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
                let Some(origin) = origins.origin_of(operand) else {
                    continue;
                };
                if !tracked.contains(&origin.root) {
                    continue;
                }
                uses.entry(origin.root).or_default().insert(block);
                match clone_borrow::access(operation, position, &roles, func, &origins, summary_of)
                {
                    Access::Escape => {
                        escaped.insert(origin.root);
                    }
                    Access::Write => {
                        writes.entry(origin.root).or_default().push(site);
                    }
                    Access::Read | Access::ReadMutable => {}
                }
            }
        }
        if !matches!(basic.terminator().kind, TerminatorKind::Invoke { .. }) {
            for operand in basic.terminator().operands() {
                if let Some(origin) = origins.origin_of(operand) {
                    if tracked.contains(&origin.root) {
                        uses.entry(origin.root).or_default().insert(block);
                        escaped.insert(origin.root);
                    }
                }
            }
        }
    }
    let mut preserving = FxHashMap::default();
    let mut loop_storage = FxHashMap::default();
    let mut preheader_writes = FxHashMap::default();
    let mut moved: FxHashMap<OperationSite, BlockId> = FxHashMap::default();
    let mut ordered = Vec::new();
    for site in candidates {
        let operation = &func.block(site.block).operations()[site.index.as_index()];
        let source = &operation.operands[0];
        let Some(origin) = origins.origin_of(source) else {
            continue;
        };
        if !origin.structural || escaped.contains(&origin.root) {
            continue;
        }
        for natural in loops
            .iter()
            .rev()
            .filter(|natural| natural.blocks.contains(&site.block))
        {
            if writes.get(&origin.root).is_some_and(|sites| {
                sites
                    .iter()
                    .any(|site| natural.blocks.contains(&site.block))
            }) {
                continue;
            }
            let mut storage = None;
            let mut inputs = Vec::new();
            if matches!(operation.kind, OperationKind::Memcpy) {
                let mir::Value::Register(destination) = operation.operands[1] else {
                    continue;
                };
                let Some(alloca) = allocas.get(&destination) else {
                    continue;
                };
                let root = Root::Alloca(destination);
                if !alloca.is_static
                    || escaped.contains(&root)
                    || writes
                        .get(&root)
                        .is_none_or(|writes| writes.as_slice() != [site])
                    || uses.get(&root).is_some_and(|blocks| {
                        blocks.iter().any(|block| !natural.blocks.contains(block))
                    })
                {
                    continue;
                }
                if natural.blocks.contains(&alloca.site.block) {
                    if !definition_dominates(alloca.site, site, dominance) {
                        continue;
                    }
                    storage = Some(alloca.site);
                } else {
                    inputs.push(&operation.operands[1]);
                }
            }
            match origin.root {
                Root::Parameter(id)
                    if matches!(
                        func.parameters()[id.as_index()].kind,
                        ParameterKind::Parameter(ArgConvention::Let)
                    ) => {}
                Root::Alloca(id) => {
                    let Some(alloca) = allocas.get(&id) else {
                        continue;
                    };
                    // A whole initialization in this straight-line preheader makes speculation
                    // safe even when the loop takes zero iterations. Partial field stores do not.
                    if alloca.site.block != natural.preheader || !alloca.is_static {
                        continue;
                    }
                    let last = writes.get(&origin.root).and_then(|sites| {
                        sites
                            .iter()
                            .filter(|site| site.block == natural.preheader)
                            .max_by_key(|site| site.index.as_index())
                    });
                    let Some(last) = last else {
                        continue;
                    };
                    let Some(initializer) = func
                        .block(last.block)
                        .operations()
                        .get(last.index.as_index())
                    else {
                        continue;
                    };
                    if !initializes_whole(initializer, id) {
                        continue;
                    }
                    let safe = preserving
                        .entry(id)
                        .or_insert_with(|| stack_region::restores_preserving_alloca(func, id));
                    let storage = loop_storage
                        .entry(natural.preheader)
                        .or_insert_with(|| LoopStorage::of(func, natural, &definitions));
                    if storage.restores.iter().any(|site| !safe.contains(site)) {
                        continue;
                    }
                }
                _ => continue,
            }
            let mut projections = Vec::new();
            if !invariant_place(
                source,
                func,
                &definitions,
                dominance,
                natural,
                &mut projections,
            ) {
                continue;
            }
            let insertion = if storage.is_some() {
                let base = projections.first().map_or(source, |site| {
                    &func.block(site.block).operations()[site.index.as_index()].operands[0]
                });
                inputs.push(base);
                let roots = roots.get_or_init(|| PlaceRoots::of(func));
                let preheader_writes =
                    preheader_writes
                        .entry(natural.preheader)
                        .or_insert_with(|| {
                            writes_in(func, &FxHashSet::from_iter([natural.preheader]), roots)
                        });
                let storage = loop_storage
                    .entry(natural.preheader)
                    .or_insert_with(|| LoopStorage::of(func, natural, &definitions));
                let Some(insertion) = insertion_point(
                    natural,
                    &definitions,
                    dominance,
                    &inputs,
                    roots,
                    preheader_writes,
                    storage,
                ) else {
                    continue;
                };
                if let Root::Alloca(_) = origin.root {
                    if writes.get(&origin.root).is_some_and(|sites| {
                        sites.iter().any(|site| {
                            site.block == natural.preheader
                                && site.index.as_index() >= insertion.as_index()
                        })
                    }) {
                        continue;
                    }
                }
                insertion
            } else {
                OperationIndex::from_index(func.block(natural.preheader).operations().len())
            };
            if let Some(storage) = storage {
                projections.push(storage);
            }
            projections.push(site);
            // Shared projections may require a different insertion point. Keep plans independent.
            if projections.iter().any(|site| moved.contains_key(site)) {
                continue;
            }
            for site in projections {
                moved.insert(site, natural.preheader);
                ordered.push((site, natural.preheader, insertion));
            }
            break;
        }
    }
    if ordered.is_empty() {
        return None;
    }
    let mut insertions: FxHashMap<OperationSite, Vec<Operation>> = FxHashMap::default();
    for (site, target, insertion) in ordered {
        insertions
            .entry(OperationSite {
                block: target,
                index: insertion,
            })
            .or_default()
            .push(func.block(site.block).operations()[site.index.as_index()].clone());
    }
    let mut edit = FunctionEdit::new(func.clone());
    for block in func.blocks() {
        let basic = func.block(block);
        let mut operations = Vec::new();
        for index in 0..=basic.operations().len() {
            let site = OperationSite {
                block,
                index: OperationIndex::from_index(index),
            };
            operations.extend(insertions.remove(&site).into_iter().flatten());
            if index < basic.operations().len() && !moved.contains_key(&site) {
                operations.push(basic.operations()[index].clone());
            }
        }
        edit.block_mut(block).operations = operations;
    }
    Some(edit.finish_unverified())
}

fn initializes_whole(operation: &Operation, root: ValueId) -> bool {
    let destination = match &operation.kind {
        OperationKind::Store | OperationKind::Memcpy | OperationKind::Clone { .. } => {
            operation.operands.get(1)
        }
        OperationKind::BuildArray { .. } => operation.operands.last(),
        OperationKind::Call { ty, .. } => {
            dataflow::call_operands(&operation.operands, ty).map(|call| call.result)
        }
        _ => None,
    };
    destination == Some(&mir::Value::Register(root))
}

/// Only static product paths may move with a load. Variant payloads can be absent on a zero-trip
/// path; dynamic addresses and layout witnesses need independent availability proofs.
fn invariant_place(
    source: &mir::Value,
    func: &Function,
    definitions: &FxHashMap<ValueId, OperationSite>,
    dominance: &Dominance,
    natural: &NaturalLoop,
    projections: &mut Vec<OperationSite>,
) -> bool {
    let mir::Value::Register(id) = source else {
        return matches!(source, mir::Value::Parameter(id)
            if matches!(func.parameters()[id.as_index()].kind,
                ParameterKind::Parameter(ArgConvention::Let)));
    };
    let Some(site) = definitions.get(id).copied() else {
        return false;
    };
    let inside = natural.blocks.contains(&site.block);
    if !inside
        && site.block != natural.preheader
        && !dominance.dominates(site.block.as_index(), natural.preheader.as_index())
    {
        return false;
    }
    let operation = &func.block(site.block).operations()[site.index.as_index()];
    if matches!(operation.kind, OperationKind::Alloca { .. }) {
        // These are the same source-root restrictions checked by the full proof below. Reject
        // them before deriving roles, provenance and accesses for a body with no other candidate.
        return site.block == natural.preheader && operation.operands.is_empty();
    }
    if !matches!(
        operation.kind,
        OperationKind::Subfield {
            variant_payload: false,
            has_layout_witness: false,
            ..
        }
    ) || operation.operands.len() != 2
        || !matches!(operation.operands[1], mir::Value::Constant(_))
        || !invariant_place(
            &operation.operands[0],
            func,
            definitions,
            dominance,
            natural,
            projections,
        )
    {
        return false;
    }
    if inside {
        projections.push(site);
    }
    true
}

fn eligible_call<'a>(
    operation: &'a Operation,
    env: ModuleEnv<'_>,
    will_return: &impl Fn(FunctionId) -> bool,
    is_optimization_barrier: &impl Fn(FunctionId) -> bool,
) -> Option<dataflow::CallOperands<'a>> {
    let OperationKind::Call { ty, metadata } = &operation.kind else {
        return None;
    };
    if !ty.effects().is_empty()
        || ty.result_convention != CallResultConvention::Value
        || !concrete_type_is_trivial_copy(ty.ret(), &env)
        || metadata
            .as_deref()
            // Vacuous in today's pipeline because whole-module owned-argument forwarding runs
            // after LICM. Retain the guard so a future reordering stays conservative.
            .is_some_and(|metadata| !metadata.owned_arguments.is_empty())
    {
        return None;
    }
    let call = dataflow::call_operands(&operation.operands, ty)?;
    if call
        .arguments
        .iter()
        .any(|(_, convention)| *convention != ArgConvention::Let)
    {
        return None;
    }
    let mir::Value::Function(callee) = call.callee else {
        return None;
    };
    if is_optimization_barrier(*callee) {
        return None;
    }
    if !will_return(*callee) {
        return None;
    }
    Some(call)
}

fn find_hoist(
    func: &Function,
    env: ModuleEnv<'_>,
    will_return: &impl Fn(FunctionId) -> bool,
    is_optimization_barrier: &impl Fn(FunctionId) -> bool,
    analysis: &LoopAnalysis,
) -> Option<Hoist> {
    let dominance = &analysis.dominance;
    let roots = PlaceRoots::of(func);
    let (definitions, allocas) = definitions(func);
    let root_blocks = OnceCell::new();
    let local = OnceCell::new();
    let values = OnceCell::new();
    for natural in &analysis.loops {
        let writes = writes_in(func, &natural.blocks, &roots);
        let preheader_writes = writes_in(func, &FxHashSet::from_iter([natural.preheader]), &roots);
        let storage = OnceCell::new();
        for block in func.blocks().filter(|block| natural.blocks.contains(block)) {
            for (index, operation) in func.block(block).operations().iter().enumerate() {
                let call_site = OperationSite {
                    block,
                    index: OperationIndex::from_index(index),
                };
                let Some(call) =
                    eligible_call(operation, env, will_return, is_optimization_barrier)
                else {
                    continue;
                };
                let mir::Value::Register(result) = call.result else {
                    continue;
                };
                let Some(alloca) = allocas.get(result).copied() else {
                    continue;
                };
                if !alloca.is_static
                    || alloca.ty
                        != match &operation.kind {
                            OperationKind::Call { ty, .. } => ty.ret(),
                            _ => unreachable!(),
                        }
                    || !concrete_type_is_trivial_copy(alloca.ty, &env)
                {
                    continue;
                }
                let output_root = Root::Alloca(*result);
                if writes
                    .get(&output_root)
                    .is_none_or(|sites| sites.as_slice() != [call_site])
                    || root_blocks
                        .get_or_init(|| RootBlocks::of(func, &roots))
                        .used_outside(output_root, &natural.blocks)
                {
                    continue;
                }

                let mut inputs = Vec::new();
                let mut operations = Vec::new();
                let admitted = call
                    .extras
                    .iter()
                    .chain(call.arguments.iter().map(|(argument, _)| *argument))
                    .all(|input| match roots.root_of(input) {
                        None => false,
                        Some(root) if root == output_root => false,
                        Some(root) if !writes.contains_key(&root) => {
                            inputs.push(input);
                            true
                        }
                        Some(_) => {
                            let values = values.get_or_init(|| {
                                ValueCells::of_matching(
                                    func,
                                    env,
                                    local.get_or_init(|| {
                                        LocalCells::of_matching(func, |_, allocation| {
                                            matches!(
                                                allocation,
                                                Allocation::Value {
                                                    witnessed: false,
                                                    ..
                                                }
                                            )
                                        })
                                    }),
                                    invariant_cell_access,
                                    || dominance,
                                )
                            });
                            invariant_cell(
                                func,
                                input,
                                values,
                                &allocas,
                                natural,
                                &mut inputs,
                                &mut operations,
                            )
                        }
                    });
                if !admitted {
                    continue;
                }

                let move_alloca = natural.blocks.contains(&alloca.site.block);
                if move_alloca {
                    if !definition_dominates(alloca.site, call_site, dominance) {
                        continue;
                    }
                    operations.push(alloca.site);
                } else {
                    inputs.push(call.result);
                }
                operations.push(call_site);
                let Some(insertion) = insertion_point(
                    natural,
                    &definitions,
                    dominance,
                    &inputs,
                    &roots,
                    &preheader_writes,
                    storage.get_or_init(|| LoopStorage::of(func, natural, &definitions)),
                ) else {
                    continue;
                };
                return Some(Hoist {
                    operations,
                    preheader: natural.preheader,
                    insertion,
                });
            }
        }
    }
    None
}

/// Accesses a hoisted definition preserves: one store or copy, then reads in every iteration. A
/// `move` out leaves the cell uninitialized for the next iteration, whatever the type.
fn invariant_cell_access(access: local_cells::Access) -> bool {
    !matches!(
        access,
        local_cells::Access::Write(local_cells::Write::CallResult)
            | local_cells::Access::MoveOut(_)
            | local_cells::Access::Callee
            | local_cells::Access::Drop
    )
}

/// Whether `input`, written in `natural`, is a value cell whose definition can move ahead of the
/// call, recording that definition and any loop-local allocation in `operations` and the inputs
/// the insertion point must follow in `inputs`.
///
/// The definition dominates every use and stores a value available before the loop, so executing
/// it once in the preheader leaves each read unchanged; a zero-trip loop reads nothing. All uses
/// stay in the loop, whose stack regions the insertion point respects as for a call's result.
fn invariant_cell<'f>(
    func: &'f Function,
    input: &'f mir::Value,
    values: &ValueCells<'_>,
    allocas: &FxHashMap<ValueId, Alloca>,
    natural: &NaturalLoop,
    inputs: &mut Vec<&'f mir::Value>,
    operations: &mut Vec<OperationSite>,
) -> bool {
    let mir::Value::Register(id) = input else {
        return false;
    };
    let (Some(cell), Some(alloca)) = (values.get(*id), allocas.get(id)) else {
        return false;
    };
    if !natural.blocks.contains(&cell.site.block) || !alloca.is_static {
        return false;
    }
    if operations.contains(&cell.site) {
        return true;
    }
    match cell.definition {
        Definition::Constant(_) | Definition::Function(_) => {}
        Definition::Register(_) => {
            inputs.push(&value_cells::operation_at(func, cell.site).operands[0])
        }
        Definition::Copy(_) | Definition::CallResult => return false,
    }
    if values
        .uses(cell)
        .iter()
        .any(|cell_use| !natural.blocks.contains(&cell_use.site.block))
    {
        return false;
    }
    if natural.blocks.contains(&alloca.site.block) {
        operations.push(alloca.site);
    } else {
        inputs.push(input);
    }
    operations.push(cell.site);
    true
}

fn definitions(
    func: &Function,
) -> (
    FxHashMap<ValueId, OperationSite>,
    FxHashMap<ValueId, Alloca>,
) {
    let mut definitions = FxHashMap::default();
    let mut allocas = FxHashMap::default();
    for block in func.blocks() {
        for (index, operation) in func.block(block).operations().iter().enumerate() {
            let Some(result) = operation.result_id() else {
                continue;
            };
            let site = OperationSite {
                block,
                index: OperationIndex::from_index(index),
            };
            definitions.insert(result, site);
            if let OperationKind::Alloca { ty } = operation.kind {
                allocas.insert(
                    result,
                    Alloca {
                        site,
                        ty,
                        is_static: operation.operands.is_empty(),
                    },
                );
            }
        }
    }
    (definitions, allocas)
}

fn writes_in(
    func: &Function,
    blocks: &FxHashSet<BlockId>,
    roots: &PlaceRoots,
) -> FxHashMap<Root, Vec<OperationSite>> {
    let mut writes = FxHashMap::<Root, Vec<OperationSite>>::default();
    for &block in blocks {
        let basic = func.block(block);
        for (index, operation) in basic.operations().iter().enumerate() {
            record_writes(
                operation,
                OperationSite {
                    block,
                    index: OperationIndex::from_index(index),
                },
                roots,
                &mut writes,
            );
        }
        if let TerminatorKind::Invoke { operation, .. } = &basic.terminator().kind {
            record_writes(
                operation,
                OperationSite {
                    block,
                    index: OperationIndex::from_index(basic.operations().len()),
                },
                roots,
                &mut writes,
            );
        } else if let TerminatorKind::Yield { place, .. } = &basic.terminator().kind
            && let Some(root) = roots.root_of(place)
        {
            writes.entry(root).or_default().push(OperationSite {
                block,
                index: OperationIndex::from_index(basic.operations().len()),
            });
        }
    }
    writes
}

fn record_writes(
    operation: &Operation,
    site: OperationSite,
    roots: &PlaceRoots,
    writes: &mut FxHashMap<Root, Vec<OperationSite>>,
) {
    let mut write = |value: &mir::Value| {
        if let Some(root) = roots.root_of(value) {
            writes.entry(root).or_default().push(site);
        }
    };
    match &operation.kind {
        OperationKind::Call { ty, metadata } => {
            let Some(call) = dataflow::call_operands(&operation.operands, ty) else {
                operation.operands.iter().for_each(&mut write);
                return;
            };
            write(call.result);
            for (argument, convention) in &call.arguments {
                if *convention == ArgConvention::MutableRef {
                    write(argument);
                }
            }
            if let Some(metadata) = metadata.as_deref() {
                for argument in metadata.owned_arguments.iter_ones() {
                    if let Some((argument, _)) = call.arguments.get(argument) {
                        write(argument);
                    }
                }
            }
        }
        OperationKind::Store | OperationKind::Memcpy | OperationKind::Clone { .. } => {
            write(&operation.operands[1]);
        }
        OperationKind::Move | OperationKind::MoveBytes { .. } | OperationKind::Replace => {
            write(&operation.operands[0]);
            write(&operation.operands[1]);
        }
        OperationKind::Clear
        | OperationKind::Drop { .. }
        | OperationKind::DropInitialized { .. }
        | OperationKind::DropSubscriptEnv
        | OperationKind::DropClosureEnv => write(&operation.operands[0]),
        OperationKind::RuntimeDealloc => write(&operation.operands[0]),
        OperationKind::BuildArray { .. } => {
            if let Some(destination) = operation.operands.last() {
                write(destination);
            }
        }
        // These operations may consume captures or run scoped mutation. Treat every rooted operand
        // as changed rather than teaching LICM another operation's ownership contract.
        OperationKind::Project { .. }
        | OperationKind::EndProject
        | OperationKind::BuildDictionary { .. }
        | OperationKind::BuildSubscriptEvidence { .. }
        | OperationKind::BuildSubscript { .. }
        | OperationKind::BuildClosure { .. } => operation.operands.iter().for_each(write),
        OperationKind::Alloca { .. }
        | OperationKind::AllocaPlace { .. }
        | OperationKind::RuntimeAlloc { .. }
        | OperationKind::BlackBox { .. }
        | OperationKind::CompareEqual
        | OperationKind::Load
        | OperationKind::Subfield { .. }
        | OperationKind::AddressOffset { .. }
        | OperationKind::AddressOffsetPlace { .. }
        | OperationKind::DictEntry { .. }
        | OperationKind::SubscriptMember { .. }
        | OperationKind::BorrowSubscriptMember { .. }
        | OperationKind::Variant { .. }
        | OperationKind::ExtractTag
        | OperationKind::ExtractPayloadIndirection
        | OperationKind::IsInitialized
        | OperationKind::StackSave
        | OperationKind::StackRestore
        | OperationKind::CheckCallDepth
        | OperationKind::CheckFuel
        | OperationKind::CloneSubscriptEnv { .. }
        | OperationKind::CloneClosureEnv { .. } => {}
    }
}

/// The blocks using each storage root, in block order.
struct RootBlocks(FxHashMap<Root, Vec<BlockId>>);

impl RootBlocks {
    fn of(func: &Function, roots: &PlaceRoots) -> Self {
        let mut blocks = FxHashMap::<Root, Vec<BlockId>>::default();
        for block in func.blocks() {
            let basic = func.block(block);
            for operand in basic
                .operations()
                .iter()
                .flat_map(|operation| operation.operands.iter())
                .chain(basic.terminator().operands())
            {
                if let Some(root) = roots.root_of(operand) {
                    let using = blocks.entry(root).or_default();
                    if using.last() != Some(&block) {
                        using.push(block);
                    }
                }
            }
        }
        Self(blocks)
    }

    fn used_outside(&self, root: Root, blocks: &FxHashSet<BlockId>) -> bool {
        self.0
            .get(&root)
            .is_some_and(|using| using.iter().any(|block| !blocks.contains(block)))
    }
}

fn definition_dominates(
    definition: OperationSite,
    usage: OperationSite,
    dominance: &Dominance,
) -> bool {
    if definition.block == usage.block {
        definition.index.as_index() < usage.index.as_index()
    } else {
        dominance.dominates(definition.block.as_index(), usage.block.as_index())
    }
}

fn insertion_point(
    natural: &NaturalLoop,
    definitions: &FxHashMap<ValueId, OperationSite>,
    dominance: &Dominance,
    inputs: &[&mir::Value],
    roots: &PlaceRoots,
    preheader_writes: &FxHashMap<Root, Vec<OperationSite>>,
    storage: &LoopStorage,
) -> Option<OperationIndex> {
    let mut earliest = 0usize;
    for &operand in inputs {
        if let mir::Value::Register(register) = operand {
            let definition = *definitions.get(register)?;
            if definition.block == natural.preheader {
                earliest = earliest.max(definition.index.as_index() + 1);
            } else if !dominance
                .dominates(definition.block.as_index(), natural.preheader.as_index())
            {
                return None;
            }
        }
        if let Some(writes) = roots
            .root_of(operand)
            .and_then(|root| preheader_writes.get(&root))
        {
            earliest = earliest.max(
                writes
                    .iter()
                    .map(|site| site.index.as_index() + 1)
                    .max()
                    .unwrap_or(0),
            );
        }
    }

    let latest = storage.insertion_limit?.as_index();
    // Insert as late as possible. Besides shortening the allocation's lifetime, this retains every
    // preheader computation and possible source failure before the speculative call while still
    // placing its storage ahead of a marker restored on the loop backedge.
    (earliest <= latest).then(|| OperationIndex::from_index(latest))
}

fn apply_hoist(func: &Function, hoist: Hoist) -> Function {
    let mut edit = FunctionEdit::new(func.clone());
    let operations: Vec<_> = hoist
        .operations
        .iter()
        .map(|site| func.block(site.block).operations()[site.index.as_index()].clone())
        .collect();
    // Every moved operation is in the loop, so removals leave the preheader's indices intact.
    let mut removed = hoist.operations;
    removed.sort_by_key(|site| (site.block.as_index(), site.index.as_index()));
    for site in removed.into_iter().rev() {
        edit.block_mut(site.block)
            .operations
            .remove(site.index.as_index());
    }
    edit.block_mut(hoist.preheader).operations.splice(
        hoist.insertion.as_index()..hoist.insertion.as_index(),
        operations,
    );
    edit.finish_unverified()
}

#[cfg(test)]
mod tests {
    use super::super::provenance::ResultProvenance;
    use super::*;
    use crate::{
        CompilerSession, Location, MirOptimization,
        hir::value::LiteralValue,
        mir::{Operation, Value, builder::FunctionBuilder, terminator::Terminator},
        module::{LocalFunctionId, ModuleId},
        std::{logic::bool_type, math::int_type},
        types::{
            effects::no_effects,
            r#type::{CallImplType, FnType},
        },
    };

    fn hoist_reads(function: &Function, env: ModuleEnv<'_>) -> Option<Function> {
        hoist_invariant_loads(
            function,
            env,
            &|_| AddressorSummary {
                provenance: ResultProvenance::Unknown,
                repeatable: false,
            },
            &LoopAnalysis::of(function),
        )
    }

    fn optimized(src: &str) -> String {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        session.emit_mir("licm", src)
    }

    fn body_of<'a>(module: &'a str, name: &str) -> &'a str {
        module
            .split(&format!("fn {name}"))
            .nth(1)
            .unwrap_or_else(|| panic!("module has no `{name}`:\n{module}"))
    }

    /// Positions of a direct call and the allocation passed as its trailing result place.
    fn call_and_result_alloca(body: &str, callee: &str) -> (usize, usize) {
        let call = body
            .find(callee)
            .unwrap_or_else(|| panic!("body has no `{callee}` call:\n{body}"));
        let line = &body[call..body[call..].find('\n').map_or(body.len(), |end| call + end)];
        let result = line
            .trim_end_matches(')')
            .rsplit_once(", ")
            .map(|(_, result)| result)
            .unwrap_or_else(|| panic!("call has no result operand: {line}"));
        // A definition renders as `%rN: <role> = alloca ...`, so the role annotation sits between
        // the register and its operation.
        let alloca = body
            .find(&format!("{result}: "))
            .filter(|start| body[*start..].starts_with(&format!("{result}: place ")))
            .filter(|start| {
                body[*start..]
                    .split_once(" = ")
                    .is_some_and(|(_, rest)| rest.starts_with("alloca"))
            })
            .unwrap_or_else(|| panic!("call result {result} has no allocation:\n{body}"));
        (call, alloca)
    }

    #[test]
    fn hoists_an_initialized_scalar_load_and_preserves_local_restores() {
        for (local, changing) in [(false, false), (true, false), (true, true)] {
            let session = CompilerSession::new();
            let env = session.module_env();
            let span = Location::new_synthesized();
            let mut builder = FunctionBuilder::new("scalar_read".into(), Default::default());
            let int_ty = int_type();
            let input = mir::Value::Parameter(
                builder.add_parameter(int_ty, ParameterKind::Parameter(ArgConvention::Let)),
            );
            let entry = builder.add_block();
            let head = builder.add_block();
            let source = if local {
                let source = builder
                    .append_operation(entry, Operation::alloca(span, int_ty))
                    .unwrap();
                builder.append_operation(
                    entry,
                    Operation::memcpy(span, input.clone(), source.clone()),
                );
                source
            } else {
                input.clone()
            };
            let marker = builder
                .append_operation(entry, Operation::stack_save(span))
                .unwrap();
            builder.set_terminator(entry, Terminator::goto(span, head));
            if changing {
                builder.append_operation(head, Operation::memcpy(span, input, source.clone()));
            }
            builder.append_operation(head, Operation::load(span, source));
            builder.append_operation(head, Operation::stack_restore(span, marker));
            builder.set_terminator(head, Terminator::goto(span, head));
            let function = builder.finish(env);
            let hoisted = hoist_reads(&function, env);
            if changing {
                assert!(hoisted.is_none());
                continue;
            }
            let hoisted = hoisted.unwrap();
            assert!(
                hoisted
                    .block(entry)
                    .operations()
                    .iter()
                    .any(|op| matches!(op.kind, OperationKind::Load))
            );
            assert!(
                !hoisted
                    .block(head)
                    .operations()
                    .iter()
                    .any(|op| matches!(op.kind, OperationKind::Load))
            );
            crate::mir::verify::verify_function(&hoisted, env);
        }
    }

    /// Split at the first loop's block header, without assuming its numeric block id.
    fn before_first_loop(body: &str) -> (&str, &str) {
        let fuel = body.find("check_fuel").expect("the loop checks fuel");
        let header = body[..fuel].rfind("\n  b").expect("the loop has a block");
        body.split_at(header)
    }

    #[test]
    fn call_motion_rebuilds_positions_after_read_motion_shifts_the_marker() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        let int_ty = int_type();
        let mut builder = FunctionBuilder::new("read_then_call".into(), Default::default());
        let input = mir::Value::Parameter(
            builder.add_parameter(int_ty, ParameterKind::Parameter(ArgConvention::Let)),
        );
        let entry = builder.add_block();
        let head = builder.add_block();
        let marker = builder
            .append_operation(entry, Operation::stack_save(span))
            .unwrap();
        builder.set_terminator(entry, Terminator::goto(span, head));
        let copy = builder
            .append_operation(head, Operation::alloca(span, int_ty))
            .unwrap();
        builder.append_operation(head, Operation::memcpy(span, input.clone(), copy.clone()));
        let result = builder
            .append_operation(head, Operation::alloca(span, int_ty))
            .unwrap();
        let (callee, ty) = session.known_callees().int_add();
        builder.append_operation(
            head,
            Operation::call(
                span,
                mir::Value::Function(callee),
                [copy, input, result],
                ty.clone(),
            ),
        );
        builder.append_operation(head, Operation::stack_restore(span, marker));
        builder.set_terminator(head, Terminator::goto(span, head));
        let function = builder.finish(env);
        let reads = hoist_reads(&function, env).unwrap();
        assert!(matches!(
            reads.block(entry).operations()[2].kind,
            OperationKind::StackSave
        ));
        assert!(
            reads
                .block(head)
                .operations()
                .iter()
                .any(|op| matches!(op.kind, OperationKind::Call { .. }))
        );
        let combined =
            hoist_loop_invariants(&function, env, &|id| id == callee, &|_| false, &|_| {
                AddressorSummary::UNKNOWN
            })
            .unwrap();
        let operations = combined.block(entry).operations();
        let call = operations
            .iter()
            .position(|op| matches!(op.kind, OperationKind::Call { .. }))
            .unwrap();
        let marker = operations
            .iter()
            .position(|op| matches!(op.kind, OperationKind::StackSave))
            .unwrap();
        assert!(
            call < marker,
            "the call and its storage must precede the shifted marker"
        );
        assert!(
            !combined
                .block(head)
                .operations()
                .iter()
                .any(|op| matches!(op.kind, OperationKind::Call { .. }))
        );
        crate::mir::verify::verify_function(&combined, env);
    }

    #[test]
    fn hoists_array_metadata_copies_with_their_storage() {
        let module = optimized(
            r#"
            fn sum_lengths(values: [int], n: int) -> int {
                let mut total = 0;
                for i in 0..n { total += len(values) + i };
                total
            }
            "#,
        );
        let body = body_of(&module, "sum_lengths")
            .split("\n\nfn ")
            .next()
            .unwrap();
        let (preheader, loop_body) = before_first_loop(body);
        assert!(
            preheader.contains("subfield") && preheader.contains("memcpy"),
            "{body}"
        );
        // No projection of the immutable array parameter remains in any loop block.
        assert!(
            !loop_body
                .lines()
                .any(|line| line.contains("subfield") && line.contains("from %p0")),
            "{body}"
        );
    }

    #[test]
    fn retains_guarded_variant_payload_reads() {
        let module = optimized(
            r#"
            fn optional(value: Option<int>, n: int) -> int {
                let mut total = 0;
                for i in 0..n {
                    match value { Some(x) => { total += x }, None => {} };
                };
                total
            }
            "#,
        );
        let body = body_of(&module, "optional")
            .split("\n\nfn ")
            .next()
            .unwrap();
        let (preheader, loop_body) = before_first_loop(body);
        assert!(!preheader.contains("variant_payload from %p0"), "{body}");
        assert!(loop_body.contains("variant_payload from %p0"), "{body}");
    }

    #[test]
    fn retains_metadata_reads_of_a_mutated_array() {
        let module = optimized(
            r#"
            fn growing(values: &mut [int], n: int) -> int {
                let mut total = 0;
                for i in 0..n { total += len(values); array_append(values, i); };
                total
            }
            "#,
        );
        let body = body_of(&module, "growing").split("\n\nfn ").next().unwrap();
        let (_, loop_body) = before_first_loop(body);
        assert!(loop_body.contains("subfield"), "{body}");
    }

    enum LocalBoundary {
        OlderRestore,
        PartialInitialization,
        EscapingPointer,
    }

    fn local_read_at_boundary(boundary: LocalBoundary, env: ModuleEnv<'_>) -> Function {
        let span = Location::new_synthesized();
        let int_ty = int_type();
        let mut builder = FunctionBuilder::new("local_boundary".into(), Default::default());
        let input = mir::Value::Parameter(
            builder.add_parameter(int_ty, ParameterKind::Parameter(ArgConvention::Let)),
        );
        let entry = builder.add_block();
        let head = builder.add_block();
        let marker = matches!(boundary, LocalBoundary::OlderRestore).then(|| {
            builder
                .append_operation(entry, Operation::stack_save(span))
                .unwrap()
        });
        let partial = matches!(boundary, LocalBoundary::PartialInitialization);
        let source_ty = if partial {
            Type::tuple([int_ty, int_ty])
        } else {
            int_ty
        };
        let root = builder
            .append_operation(entry, Operation::alloca(span, source_ty))
            .unwrap();
        let source = if partial {
            let index = mir::Value::Constant(builder.add_constant(
                int_ty,
                LiteralValue::new_native(0isize),
                &env,
            ));
            builder
                .append_operation(
                    entry,
                    Operation::product_subfield(span, root, index, int_ty, source_ty, []),
                )
                .unwrap()
        } else {
            root
        };
        builder.append_operation(entry, Operation::memcpy(span, input, source.clone()));
        if matches!(boundary, LocalBoundary::EscapingPointer) {
            let slot = builder
                .append_operation(entry, Operation::alloca_place(span, int_ty))
                .unwrap();
            builder.append_operation(entry, Operation::store(span, source.clone(), slot));
        }
        builder.set_terminator(entry, Terminator::goto(span, head));
        builder.append_operation(head, Operation::load(span, source));
        if let Some(marker) = marker {
            builder.append_operation(head, Operation::stack_restore(span, marker));
        }
        builder.set_terminator(head, Terminator::goto(span, head));
        builder.finish(env)
    }

    #[test]
    fn retains_a_local_read_invalidated_by_an_older_restore() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let function = local_read_at_boundary(LocalBoundary::OlderRestore, env);
        assert!(hoist_reads(&function, env).is_none());
    }

    #[test]
    fn retains_a_read_of_a_partially_initialized_local() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let function = local_read_at_boundary(LocalBoundary::PartialInitialization, env);
        assert!(hoist_reads(&function, env).is_none());
    }

    #[test]
    fn retains_a_read_of_an_escaping_local() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let function = local_read_at_boundary(LocalBoundary::EscapingPointer, env);
        assert!(hoist_reads(&function, env).is_none());
    }

    #[test]
    fn hoists_independent_reads_to_the_outermost_nested_preheader() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new("nested_reads".into(), Default::default());
        let int_ty = int_type();
        let input = mir::Value::Parameter(
            builder.add_parameter(int_ty, ParameterKind::Parameter(ArgConvention::Let)),
        );
        let condition = mir::Value::Parameter(
            builder.add_parameter(bool_type(), ParameterKind::Parameter(ArgConvention::Let)),
        );
        let entry = builder.add_block();
        let outer = builder.add_block();
        let inner_preheader = builder.add_block();
        let inner = builder.add_block();
        let backedge = builder.add_block();
        let exit = builder.add_block();
        builder.set_terminator(entry, Terminator::goto(span, outer));
        let test = builder
            .append_operation(outer, Operation::load(span, condition.clone()))
            .unwrap();
        builder.set_terminator(
            outer,
            Terminator::cond_br(span, test, inner_preheader, exit),
        );
        builder.set_terminator(inner_preheader, Terminator::goto(span, inner));
        builder.append_operation(inner, Operation::load(span, input));
        let test = builder
            .append_operation(inner, Operation::load(span, condition))
            .unwrap();
        builder.set_terminator(inner, Terminator::cond_br(span, test, inner, backedge));
        builder.set_terminator(backedge, Terminator::goto(span, outer));
        builder.set_terminator(exit, Terminator::ret(span));
        let function = builder.finish(env);
        let hoisted = hoist_reads(&function, env).unwrap();
        assert_eq!(
            hoisted
                .block(entry)
                .operations()
                .iter()
                .filter(|op| matches!(op.kind, OperationKind::Load))
                .count(),
            3
        );
        assert!(hoisted.block(inner_preheader).operations().is_empty());
        assert!(hoisted.block(inner).operations().is_empty());
        crate::mir::verify::verify_function(&hoisted, env);
    }

    #[test]
    fn retains_a_copy_whose_destination_is_used_after_the_loop() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        let int_ty = int_type();
        let mut builder = FunctionBuilder::new("copy_used_after_loop".into(), Default::default());
        let input = mir::Value::Parameter(
            builder.add_parameter(int_ty, ParameterKind::Parameter(ArgConvention::Let)),
        );
        let condition = mir::Value::Parameter(
            builder.add_parameter(bool_type(), ParameterKind::Parameter(ArgConvention::Let)),
        );
        let entry = builder.add_block();
        let head = builder.add_block();
        let exit = builder.add_block();
        let destination = builder
            .append_operation(entry, Operation::alloca(span, int_ty))
            .unwrap();
        builder.set_terminator(entry, Terminator::goto(span, head));
        builder.append_operation(head, Operation::memcpy(span, input, destination.clone()));
        let test = builder
            .append_operation(head, Operation::load(span, condition))
            .unwrap();
        builder.set_terminator(head, Terminator::cond_br(span, test, head, exit));
        builder.append_operation(exit, Operation::load(span, destination));
        builder.set_terminator(exit, Terminator::ret(span));
        let function = builder.finish(env);
        let hoisted = hoist_reads(&function, env).unwrap();
        // The independent condition load can move; the copy and its post-loop use must remain.
        assert!(
            hoisted
                .block(head)
                .operations()
                .iter()
                .any(|op| matches!(op.kind, OperationKind::Memcpy))
        );
        assert!(
            hoisted
                .block(exit)
                .operations()
                .iter()
                .any(|op| matches!(op.kind, OperationKind::Load))
        );
        crate::mir::verify::verify_function(&hoisted, env);
    }

    #[test]
    fn hoists_an_invariant_pure_call_before_the_loop_stack_marker() {
        // The extra addition leaves a loop-local temporary, so the marker still delimits real
        // storage after LICM and final DCE; an unread marker is no longer retained as scaffolding.
        let module = optimized(
            "fn invariant(x: int, y: int, n: int) {\n\
                 let mut total = 0;\n\
                 for i in 0..n { total = total + x * y + i };\n\
                 total\n\
             }",
        );
        let body = body_of(&module, "invariant");
        let multiply = body
            .find("call std::Num<std::int>::mul")
            .expect("the invariant multiplication remains a call");
        let marker = body
            .find("stack_save")
            .expect("the loop has a stack marker");
        assert!(
            multiply < marker,
            "the call and its result must be before the marker restored on every iteration:\n{body}"
        );
        assert_eq!(
            body.matches("call std::Num<std::int>::mul").count(),
            1,
            "LICM moves rather than duplicates the call:\n{body}"
        );
        let (_, result_alloca) = call_and_result_alloca(body, "call std::Num<std::int>::mul");
        assert!(
            result_alloca < marker,
            "a loop-local result allocation must move with the call:\n{body}"
        );
    }

    #[test]
    fn a_cell_moved_out_in_the_loop_keeps_its_definition_there() {
        // `move` leaves its source uninitialized, so the cell must be filled again each iteration.
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new("moved_cell".into(), Default::default());
        let preheader = builder.add_block();
        let body = builder.add_block();
        let constant = Value::Constant(builder.add_constant(
            int_type(),
            LiteralValue::new_native(3isize),
            &env,
        ));
        let callee = FunctionId::new(ModuleId::default(), LocalFunctionId::default());
        builder.set_terminator(preheader, Terminator::goto(span, body));
        let mut alloca = || {
            builder
                .append_operation(body, Operation::alloca(span, int_type()))
                .expect("an alloca has a result")
        };
        let (cell, result, destination) = (alloca(), alloca(), alloca());
        builder.append_operation(body, Operation::store(span, constant, cell.clone()));
        builder.append_operation(
            body,
            Operation::call(
                span,
                Value::Function(callee),
                [cell.clone(), result],
                CallImplType::value(FnType::new_mut_resolved(
                    [(int_type(), false)],
                    int_type(),
                    no_effects(),
                )),
            ),
        );
        builder.append_operation(body, Operation::move_value(span, cell, destination));
        builder.set_terminator(body, Terminator::goto(span, body));
        let function = builder.finish_unverified();

        let hoisted = hoist_loop_invariants(&function, env, &|_| true, &|_| false, &|_| {
            AddressorSummary {
                provenance: ResultProvenance::Unknown,
                repeatable: false,
            }
        });
        assert!(
            hoisted.is_none(),
            "the store refilling a moved-out cell must stay in the loop"
        );
    }

    #[test]
    fn hoists_a_call_with_its_constant_operand_cell_through_nested_loops() {
        // The constant `3` reaches the call through a cell stored in the inner loop; that store
        // is a value-cell definition and moves with the call, one loop at a time.
        let source = "fn constant_operand(a: int, n: int) {\n\
                          let mut total = 0;\n\
                          for i in 0..n {\n\
                              for j in 0..n { total = total + (a * 3) * j }\n\
                          };\n\
                          total\n\
                      }\n\
                      fn main() { constant_operand(2, 4) + constant_operand(2, 0) }";
        let module = optimized(source);
        let body = body_of(&module, "constant_operand");
        // Of the two multiplications, only the invariant one reads `a`.
        let (call, result_alloca) = call_and_result_alloca(body, "(%p0, ");
        let outer_marker = body.find("stack_save").expect("both loops have markers");
        assert!(
            call < outer_marker && result_alloca < call,
            "the call and its storage must move out of both loops:\n{body}"
        );
        let operand = body[..call]
            .rfind("store @c")
            .expect("the constant operand is stored before the call");
        assert!(
            body[operand..call].lines().count() <= 3,
            "the constant's definition must move with the call:\n{body}"
        );

        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        assert_eq!(session.eval_mir("licm_run", source), "144");
    }

    #[test]
    fn does_not_hoist_when_an_operand_changes_in_the_loop() {
        let module = optimized(
            "fn changing(mut x: int, y: int, n: int) {\n\
                 let mut total = 0;\n\
                 for i in 0..n { total = total + x * y; x = x + 1 };\n\
                 total\n\
             }",
        );
        let body = body_of(&module, "changing");
        let multiply = body
            .find("call std::Num<std::int>::mul")
            .expect("the multiplication remains");
        let marker = body
            .find("stack_save")
            .expect("the loop has a stack marker");
        assert!(
            marker < multiply,
            "a call reading a loop-carried place must remain in the loop:\n{body}"
        );
    }

    #[test]
    fn does_not_hoist_a_pure_recursive_call_out_of_a_zero_trip_loop() {
        let module = optimized(
            "fn diverges(x: int) -> int { diverges(x) }\n\
             fn retain_zero_trip(x: int, n: int) {\n\
                 let mut total = 0;\n\
                 for i in 0..n { total = total + diverges(x) };\n\
                 total\n\
             }",
        );
        let body = body_of(&module, "retain_zero_trip");
        let call = body
            .find("call licm::diverges")
            .expect("the pure call remains");
        let marker = body
            .find("stack_save")
            .expect("the loop has a stack marker");
        assert!(
            marker < call,
            "a possibly diverging call must remain guarded:\n{body}"
        );
    }

    /// The reviewer's `while i < x {}` example, expressed with Ferlium's current loop syntax.
    /// `spin(1)` does not return, but the zero-trip caller must still return without invoking it.
    #[test]
    fn conditional_spin_is_not_speculated_onto_a_zero_trip_path() {
        let source = "#[inline(never)]\n\
             fn spin(x: int) -> int {\n\
                 if x > 0 { loop {} };\n\
                 0\n\
             }\n\
             fn zero_trip(x: int, n: int) {\n\
                 let mut total = 0;\n\
                 for i in 0..n { total = total + spin(x) };\n\
                 total\n\
             }\n\
             fn main() { zero_trip(1, 0) }";

        let module = optimized(source);
        let body = body_of(&module, "zero_trip");
        let call = body
            .find("call licm::spin")
            .expect("#[inline(never)] keeps the spin call visible");
        let marker = body.find("stack_save").expect("the loop has a marker");
        assert!(
            marker < call,
            "the conditionally diverging call must remain on the entered-loop path:\n{body}"
        );

        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        assert_eq!(session.eval_mir("spin_zero_trip", source), "0");
    }

    #[test]
    fn hoists_a_proved_terminating_script_call() {
        // Costlier than the inliner's per-callee budget, so the direct script call reaches LICM.
        // Its raw MIR is nevertheless an acyclic call DAG and proves `will_return`.
        let module = optimized(
            "fn large_sum(x: int) -> int {\n\
                 let a = x + x + x + x + x + x + x + x + x + x;\n\
                 let b = a + x + x + x + x + x + x + x + x + x + x;\n\
                 let c = b + x + x + x + x + x + x + x + x + x + x;\n\
                 let d = c + x + x + x + x + x + x + x + x + x + x;\n\
                 let e = d + x + x + x + x + x + x + x + x + x + x;\n\
                 e + x + x + x + x + x + x + x + x + x + x\n\
             }\n\
             fn script_callee(x: int, n: int) {\n\
                 let mut total = 0;\n\
                 for i in 0..n { total = total + large_sum(x) };\n\
                 total\n\
             }",
        );
        let body = body_of(&module, "script_callee");
        let call = body
            .find("call licm::large_sum")
            .expect("the large script callee must remain a call");
        let header = body.find("check_fuel").expect("the loop checks fuel");
        assert!(
            call < header,
            "a generic will-return proof, not native identity, permits hoisting:\n{body}"
        );
    }

    #[test]
    fn hoists_through_nested_preheaders() {
        let module = optimized(
            "fn nested(x: int, y: int, n: int) {\n\
                 let mut total = 0;\n\
                 for i in 0..n {\n\
                     for j in 0..n { total = total + x * y }\n\
                 };\n\
                 total\n\
             }",
        );
        let body = body_of(&module, "nested");
        let call = body
            .find("call std::Num<std::int>::mul")
            .expect("the invariant multiplication remains a call");
        let outer_marker = body.find("stack_save").expect("both loops have markers");
        assert!(
            call < outer_marker,
            "the call must move out of both nested loops:\n{body}"
        );
    }

    #[test]
    fn a_restore_of_an_older_marker_prevents_inner_hoisting() {
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new("older_marker".into(), Default::default());
        let entry = builder.add_block();
        let preheader = builder.add_block();
        let head = builder.add_block();
        let backedge = builder.add_block();
        let marker = builder
            .append_operation(entry, Operation::stack_save(span))
            .expect("stack_save returns its marker");
        builder.set_terminator(entry, Terminator::goto(span, preheader));
        builder.set_terminator(preheader, Terminator::goto(span, head));
        builder.set_terminator(head, Terminator::goto(span, backedge));
        builder.append_operation(backedge, Operation::stack_restore(span, marker));
        builder.set_terminator(backedge, Terminator::goto(span, head));

        let session = CompilerSession::new();
        let function = builder.finish(session.module_env());
        let (successors, _) = cfg(&function);
        let dominance = Dominance::of(&successors, function.entry().as_index());
        let (definitions, _) = definitions(&function);
        let natural = NaturalLoop {
            blocks: FxHashSet::from_iter([head, backedge]),
            header: head,
            preheader,
        };
        assert!(
            insertion_point(
                &natural,
                &definitions,
                &dominance,
                &[],
                &PlaceRoots::of(&function),
                &FxHashMap::default(),
                &LoopStorage::of(&function, &natural, &definitions),
            )
            .is_none(),
            "storage cannot move below a marker defined before the preheader and restored in the loop"
        );
    }

    #[test]
    fn does_not_hoist_a_result_used_after_the_loop() {
        let module = optimized(
            "fn escaping_result(x: int, y: int, n: int) {\n\
                 let mut saved = 0;\n\
                 for i in 0..n { saved = x * y };\n\
                 saved\n\
             }",
        );
        let body = body_of(&module, "escaping_result");
        let call = body
            .find("call std::Num<std::int>::mul")
            .expect("the multiplication remains a call");
        let header = body.find("check_fuel").expect("the loop checks fuel");
        assert!(
            header < call,
            "a call whose result root escapes the loop must remain inside it:\n{body}"
        );
    }

    #[test]
    fn hoists_every_trivial_numeric_result_type() {
        let module = optimized(
            "fn invariant_float(x: float, y: float, n: int) {\n\
                 let mut total = 0.0;\n\
                 for i in 0..n { total = total + x * y };\n\
                 total\n\
             }",
        );
        let body = body_of(&module, "invariant_float");
        let multiply = body
            .find("call std::Num<std::float>::mul")
            .expect("the invariant float multiplication remains a call");
        let header = body.find("check_fuel").expect("the loop checks fuel");
        assert!(
            multiply < header,
            "LICM must be generic over concrete TrivialCopy result types:\n{body}"
        );
    }

    #[test]
    fn hoisted_storage_survives_iteration_restores_and_zero_trip_execution() {
        // Keep a varying intermediate result inside the loop, forcing real iteration restores.
        let source = "fn invariant(x: int, y: int, n: int) {\n\
                          let mut total = 0;\n\
                          for i in 0..n { total = total + x * y + i };\n\
                          total\n\
                      }\n\
                      fn main() { invariant(6, 7, 4) + invariant(6, 7, 0) }";
        let module = optimized(source);
        let body = body_of(&module, "invariant");
        let (_, result_alloca) = call_and_result_alloca(body, "call std::Num<std::int>::mul");
        let marker = body.find("stack_save").expect("the loop has a marker");
        assert!(body.contains("stack_restore"), "{body}");
        assert!(
            result_alloca < marker,
            "this execution test must exercise the loop-local alloca moved with its call:\n{body}"
        );

        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        assert_eq!(session.eval_mir("licm_run", source), "174");
    }
}
