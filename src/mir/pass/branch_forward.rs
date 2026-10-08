// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Forwarding of local values materialized only to select control flow.
//!
//! Lowering and inlining can turn one predicate into this diamond:
//!
//! ```text
//! condbr predicate, left, right
//! left:  store true  to flag; br join
//! right: store false to flag; br join
//! join:  stack_restore marker; equal = load flag; condbr equal, yes, no
//! ```
//!
//! The second read and branch recover information the incoming edge already carries. This pass
//! redirects each storing block to `yes` or `no`, retaining the intervening `stack_restore`s on
//! that edge. The join then becomes unreachable, and ordinary DCE removes the boolean allocation
//! and stores.
//!
//! Both forms of that read are recognized. Each names the flag and carries a polarity: a `load`
//! takes the *then* edge when the arm stored `true`, while a `comp_eq` takes it when the arm stored
//! the pattern being compared. An arm may instead store a computed boolean; it then ends in a
//! `condbr` on that value.
//!
//! A concrete `TrivialCopy` variant follows the same control shape. Each incoming path stores a
//! statically tagged shell, and the join extracts that tag only to feed `switch_variant`. The pass
//! redirects each construction path to the selected consumer while retaining payload storage for
//! projections in that consumer. A path may store its shell well above the join, and other paths
//! may meet it on the way, as in an inlined iterator `next` that stores `Some` before computing its
//! payload: a forward analysis gives the tag each block leaves, and the join's predecessors that
//! leave a known tag are redirected. Escaping storage and managed payloads are outside this rule. A
//! one-case `comp_eq` tag test is instead replaced by a boolean shadow of the variant's stores,
//! which leaves the flag shape above.
//!
//! A store need not sit in an immediate predecessor of the join. A short-circuit `or` or `and` with
//! three or more arms lowers to a *tree* of stores, whose deeper arms reach the join through a
//! block that only restores the stack:
//!
//! ```text
//! outer: condbr first, left, inner
//! inner: condbr second, right, middle
//! left:   store true  to flag; br join
//! middle: store true  to flag; br forward
//! right:  store false to flag; br forward
//! forward: stack_restore marker; br join
//! join:   equal = load flag; condbr equal, yes, no
//! ```
//!
//! So the search walks back from the join to the stores that reach it, through blocks that carry
//! only edge cleanup, and replays that cleanup on each arm it redirects.
//!
//! The proof is intentionally local and linear. The flag must be a local boolean `alloca`; every
//! use must be a boolean store, a call result destination, or the one final read; every block on a walked path
//! must end in an unconditional jump; a store-free block on a path may contain only
//! `stack_restore`s; the join may contain only `stack_restore`s besides the read; and the
//! stores found must be exactly those the use census saw, which is what proves no other definition
//! reaches the join. Two paths may not meet at one block, since rewriting it would mean duplicating
//! it. For a variant, the forward analysis takes the place of the store census: a block where
//! paths storing one tag meet leaves that tag and is redirected itself.

use rustc_hash::{FxHashMap, FxHashSet};
use ustr::Ustr;

use super::{
    dataflow::{self, Root},
    site::{OperationIndex, OperationSite},
};
use crate::{
    hir::value::LiteralValue,
    mir::{
        self, BlockId, DebugLocation, Function, Operation, OperationKind,
        edit::FunctionEdit,
        pass::budget::{FORWARD_BOOLEAN_BLOCKS, FORWARD_BOOLEAN_REPLAYED_OPERATIONS},
        terminator::{Terminator, TerminatorKind},
        value::ValueId,
    },
    module::{ModuleEnv, id::Id},
    std::logic::bool_type,
    types::type_properties::concrete_type_is_trivial_copy,
};

#[derive(Clone, Copy)]
struct Stored<T> {
    block: BlockId,
    value: T,
}

/// What one store writes into a boolean flag.
#[derive(Clone, Copy)]
enum Flag {
    Literal(bool),
    Computed(ValueId),
    CallResult(ValueId),
}

#[derive(Default)]
struct Uses {
    stores: Vec<Stored<Flag>>,
    reads: Vec<OperationSite>,
    other: bool,
}

#[derive(Default)]
struct VariantUses {
    stores: Vec<Stored<Ustr>>,
    reads: Vec<OperationSite>,
    other: bool,
}

/// One store that reaches the join, and the edge cleanup it must run in place of the blocks the
/// rewrite removes between it and the join.
struct Arm {
    source: BlockId,
    exit: Exit,
    replay: Vec<Operation>,
}

/// Where a redirected arm goes: straight to the consumer's target, or, when it stored a computed
/// boolean, to a branch on that value.
enum Exit {
    Goto(BlockId),
    TestPlace {
        place: ValueId,
        then_target: BlockId,
        else_target: BlockId,
    },
    Branch {
        condition: ValueId,
        then_target: BlockId,
        else_target: BlockId,
    },
}

struct Forward {
    arms: Vec<Arm>,
}

/// Bypasses boolean storage diamonds, returning `None` when the function has none.
pub(crate) fn forward_boolean_branches(func: &Function) -> Option<Function> {
    // Restrict the use census to local boolean storage. This takes one definition walk and one
    // operand walk; planning below only visits the uses and predecessors belonging to a candidate.
    let mut uses: FxHashMap<ValueId, Uses> = func
        .blocks()
        .flat_map(|block| func.block(block).operations())
        .filter_map(|operation| {
            if let OperationKind::Alloca { ty } = operation.kind
                && ty == bool_type()
            {
                operation.result_id().map(|id| (id, Uses::default()))
            } else {
                None
            }
        })
        .collect();
    if uses.is_empty() {
        return None;
    }
    let value_uses = census_uses(func, &mut uses);
    if !uses
        .values()
        .any(|summary| !summary.other && summary.reads.len() == 1 && summary.stores.len() >= 2)
    {
        return None;
    }
    // Building the predecessor map is a separate CFG walk. Most functions have no boolean
    // storage diamond, so defer it until the cheaper definition/use census found a viable shape.
    let incoming = incoming_predecessors(func);

    let mut forwards = Vec::new();
    for join in func.blocks() {
        if let Some(forward) = plan_join(func, join, &incoming, &uses, &value_uses) {
            forwards.push(forward);
        }
    }
    if forwards.is_empty() {
        return None;
    }

    // All plans use the original block identities. Apply every edge rewrite before the one
    // structural cleanup that renumbers blocks.
    let mut edit = FunctionEdit::new(func.clone());
    for forward in forwards {
        for arm in forward.arms {
            let span = edit.block(arm.source).terminator.span;
            let terminator = arm.exit.terminator(span, &mut edit, arm.source);
            let block = edit.block_mut(arm.source);
            block.operations.extend(arm.replay);
            block.terminator = terminator;
        }
    }
    edit.remove_unreachable_blocks();
    edit.merge_blocks_into_predecessors();
    Some(edit.finish_unverified())
}

/// Forwards a tag switch through the local variant constructions that select its result.
///
/// The variant storage must be a concrete `TrivialCopy` local whose address does not escape. Every
/// whole-place definition must store a statically tagged variant shell, and the one tag read must
/// feed the switch directly. Payload projections remain in place, so selected arms can keep using
/// their initialized payload without introducing phi values or changing ownership.
pub(crate) fn forward_variant_branches(func: &Function, env: ModuleEnv<'_>) -> Option<Function> {
    if !func.blocks().any(|block| {
        matches!(
            func.block(block).terminator().kind,
            TerminatorKind::SwitchVariant { .. }
        )
    }) {
        return None;
    }

    let mut variant_tags = FxHashMap::default();
    let mut extract_results = FxHashSet::default();
    for operation in func
        .blocks()
        .flat_map(|block| func.block(block).operations())
    {
        let Some(result) = operation.result_id() else {
            continue;
        };
        match operation.kind {
            OperationKind::Variant { tag, .. } => {
                variant_tags.insert(result, tag);
            }
            OperationKind::ExtractTag => {
                extract_results.insert(result);
            }
            _ => {}
        }
    }
    if variant_tags.len() < 2 || extract_results.is_empty() {
        return None;
    }

    let mut variant_store_counts = FxHashMap::<ValueId, usize>::default();
    for operation in func
        .blocks()
        .flat_map(|block| func.block(block).operations())
    {
        if matches!(operation.kind, OperationKind::Store)
            && let [
                mir::Value::Register(source),
                mir::Value::Register(destination),
            ] = operation.operands.as_ref()
            && variant_tags.contains_key(source)
        {
            *variant_store_counts.entry(*destination).or_default() += 1;
        }
    }
    variant_store_counts.retain(|_, count| *count >= 2);
    if variant_store_counts.is_empty() {
        return None;
    }

    // Type-property queries are more expensive than the structural gates above. Restrict them to
    // storage that already receives at least two statically tagged shells.
    let mut uses: FxHashMap<ValueId, VariantUses> = FxHashMap::default();
    for block in func.blocks() {
        for operation in func.block(block).operations() {
            if let OperationKind::Alloca { ty } = operation.kind
                && let Some(result) = operation.result_id()
                && variant_store_counts.contains_key(&result)
                && concrete_type_is_trivial_copy(ty, &env)
            {
                uses.insert(result, VariantUses::default());
            }
        }
    }
    if uses.is_empty() {
        return None;
    }

    let mut extract_uses = FxHashMap::<ValueId, usize>::default();
    for block in func.blocks() {
        let basic_block = func.block(block);
        for (index, operation) in basic_block.operations().iter().enumerate() {
            let site = OperationSite {
                block,
                index: OperationIndex::from_index(index),
            };
            for (operand_index, operand) in operation.operands.iter().enumerate() {
                let mir::Value::Register(id) = operand else {
                    continue;
                };
                if extract_results.contains(id) {
                    *extract_uses.entry(*id).or_default() += 1;
                }
                let Some(summary) = uses.get_mut(id) else {
                    continue;
                };
                match &operation.kind {
                    OperationKind::Store if operand_index == 1 => {
                        let Some(mir::Value::Register(source)) = operation.operands.first() else {
                            summary.other = true;
                            continue;
                        };
                        if let Some(tag) = variant_tags.get(source) {
                            summary.stores.push(Stored { block, value: *tag });
                        } else {
                            summary.other = true;
                        }
                    }
                    OperationKind::ExtractTag if operand_index == 0 => summary.reads.push(site),
                    OperationKind::Subfield {
                        variant_payload: true,
                        ..
                    } if operand_index == 0 => {}
                    _ => summary.other = true,
                }
            }
        }
        for operand in basic_block.terminator().operands() {
            if let mir::Value::Register(id) = operand {
                if extract_results.contains(id) {
                    *extract_uses.entry(*id).or_default() += 1;
                }
                if let Some(summary) = uses.get_mut(id) {
                    summary.other = true;
                }
            }
        }
    }
    uses.retain(|_, summary| {
        !summary.other && summary.reads.len() == 1 && summary.stores.len() >= 2
    });
    if uses.is_empty() {
        return None;
    }

    // Address escape is the boundary between this local control-flow rewrite and general variant
    // scalar replacement. The shared place analysis recognizes payload projections and passive
    // call arguments without treating them as aliases.
    let (escaped, _) = dataflow::escaping_roots(func, &|_| false);
    uses.retain(|id, _| !escaped.contains(&Root::Alloca(*id)));
    if uses.is_empty() {
        return None;
    }

    let incoming = incoming_predecessors(func);
    let forwards: Vec<_> = func
        .blocks()
        .filter_map(|join| plan_variant_join(func, join, &incoming, &uses, &extract_uses))
        .collect();
    if forwards.is_empty() {
        return None;
    }

    let mut edit = FunctionEdit::new(func.clone());
    for forward in forwards {
        for arm in forward.arms {
            let span = edit.block(arm.source).terminator.span;
            let terminator = arm.exit.terminator(span, &mut edit, arm.source);
            let block = edit.block_mut(arm.source);
            block.operations.extend(arm.replay);
            block.terminator = terminator;
        }
    }
    edit.remove_unreachable_blocks();
    edit.merge_blocks_into_predecessors();
    Some(edit.finish_unverified())
}

fn plan_variant_join(
    func: &Function,
    join: BlockId,
    incoming: &[Vec<BlockId>],
    uses: &FxHashMap<ValueId, VariantUses>,
    extract_uses: &FxHashMap<ValueId, usize>,
) -> Option<Forward> {
    let block = func.block(join);
    let read_index = block.operations().len().checked_sub(1)?;
    let read = &block.operations()[read_index];
    if !matches!(read.kind, OperationKind::ExtractTag) {
        return None;
    }
    let result = read.result_id()?;
    let TerminatorKind::SwitchVariant {
        tag: mir::Value::Register(condition),
        cases,
        default,
    } = &block.terminator().kind
    else {
        return None;
    };
    if *condition != result || extract_uses.get(&result) != Some(&1) {
        return None;
    }
    if cases.iter().any(|(_, target)| *target == join) || *default == join {
        // This rewrite removes the dispatch block. A self-edge would keep it reachable and run
        // copied stack restorations on both the predecessor and the dispatch block.
        return None;
    }

    let [mir::Value::Register(storage)] = read.operands.as_ref() else {
        return None;
    };
    let summary = uses.get(storage)?;
    let read_site = OperationSite {
        block: join,
        index: OperationIndex::from_index(read_index),
    };
    if summary.reads.as_slice() != [read_site]
        || !block.operations()[..read_index]
            .iter()
            .all(|operation| matches!(operation.kind, OperationKind::StackRestore))
    {
        return None;
    }

    let join_prefix = &block.operations()[..read_index];
    let mut arms = Vec::with_capacity(summary.stores.len());
    // The tag each path leaves decides its consumer, however far up it was stored: paths that
    // meet before the join with one tag need no duplication, and the join's predecessors are
    // redirected rather than the storing blocks. A path that does not agree on one tag is crossed
    // only through edge cleanup, as the store trees of nested constructors require.
    let tags = exit_tags(func, &summary.stores, incoming);
    let reaching = reaching_sources(func, join, incoming, |block| match tags[block.as_index()] {
        ExitTag::Known(tag) => Step::Source(tag),
        ExitTag::Unknown => Step::Cross,
        ExitTag::Unreached => Step::Refuse,
    })?;
    for reaching in reaching {
        let target = cases
            .iter()
            .find_map(|(case, target)| (*case == reaching.value).then_some(*target))
            .unwrap_or(*default);
        let mut replay = reaching.replay;
        replay.extend(join_prefix.iter().cloned());
        arms.push(Arm {
            source: reaching.source,
            exit: Exit::Goto(target),
            replay,
        });
    }
    Some(Forward { arms })
}

/// Replaces tag tests on local variants with loads of boolean shadows, returning `None` when there
/// is none.
///
/// A concrete `TrivialCopy` local written only by whole stores of statically tagged shells holds,
/// at every read, the tag of the last store; payload writes cannot change it. Pairing each store
/// with a store of the literal `tag == C` into a boolean cell keeps that cell equal to the test, so
/// `comp_eq (extract_tag v) C` becomes a load of it. The arms then carry the literal-flag shape
/// that boolean forwarding and materialization consume, and DCE collects the unread variant.
pub(crate) fn shadow_variant_tag_tests(func: &Function, env: ModuleEnv<'_>) -> Option<Function> {
    let mut variant_tags = FxHashMap::default();
    let mut tag_reads = FxHashMap::default();
    let mut allocas = FxHashMap::default();
    let mut tests = Vec::new();
    for block in func.blocks() {
        for (index, operation) in func.block(block).operations().iter().enumerate() {
            let Some(result) = operation.result_id() else {
                continue;
            };
            let site = OperationSite {
                block,
                index: OperationIndex::from_index(index),
            };
            match (&operation.kind, operation.operands.as_ref()) {
                (OperationKind::Alloca { ty }, _) => {
                    allocas.insert(result, (site, *ty));
                }
                (OperationKind::Variant { tag, .. }, _) => {
                    variant_tags.insert(result, *tag);
                }
                (OperationKind::ExtractTag, [mir::Value::Register(storage)]) => {
                    tag_reads.insert(result, *storage);
                }
                (
                    OperationKind::CompareEqual,
                    [mir::Value::Register(tag), mir::Value::Pattern(pattern)],
                ) if let Some(case) = pattern.as_variant_tag() => {
                    tests.push((site, *tag, *case));
                }
                _ => {}
            }
        }
    }
    tests.retain(|(_, tag, _)| {
        tag_reads
            .get(tag)
            .is_some_and(|storage| allocas.contains_key(storage))
    });
    if tests.is_empty() {
        return None;
    }

    // Every use of a candidate storage must be a tagged whole store, a tag read or a payload
    // projection, and every use of its tag reads a test.
    #[derive(Default)]
    struct Shadowed {
        stores: Vec<(OperationSite, Ustr)>,
        other: bool,
    }
    let mut storages: FxHashMap<ValueId, Shadowed> = tests
        .iter()
        .map(|(_, tag, _)| (tag_reads[tag], Shadowed::default()))
        .collect();
    let tested: FxHashSet<OperationSite> = tests.iter().map(|(site, ..)| *site).collect();
    for block in func.blocks() {
        let basic_block = func.block(block);
        for (index, operation) in basic_block.operations().iter().enumerate() {
            let site = OperationSite {
                block,
                index: OperationIndex::from_index(index),
            };
            for (position, operand) in operation.operands.iter().enumerate() {
                let mir::Value::Register(id) = operand else {
                    continue;
                };
                if let Some(storage) = tag_reads.get(id)
                    && !tested.contains(&site)
                    && let Some(shadowed) = storages.get_mut(storage)
                {
                    shadowed.other = true;
                }
                let Some(shadowed) = storages.get_mut(id) else {
                    continue;
                };
                match (&operation.kind, position) {
                    (OperationKind::Store, 1) => match &operation.operands[0] {
                        mir::Value::Register(shell) if let Some(tag) = variant_tags.get(shell) => {
                            shadowed.stores.push((site, *tag));
                        }
                        _ => shadowed.other = true,
                    },
                    (OperationKind::ExtractTag, 0)
                    | (
                        OperationKind::Subfield {
                            variant_payload: true,
                            ..
                        },
                        0,
                    ) => {}
                    _ => shadowed.other = true,
                }
            }
        }
        for operand in basic_block.terminator().operands() {
            if let mir::Value::Register(id) = operand {
                for storage in [tag_reads.get(id).copied(), Some(*id)]
                    .into_iter()
                    .flatten()
                {
                    if let Some(shadowed) = storages.get_mut(&storage) {
                        shadowed.other = true;
                    }
                }
            }
        }
    }
    storages.retain(|storage, shadowed| {
        !shadowed.other
            && !shadowed.stores.is_empty()
            && concrete_type_is_trivial_copy(allocas[storage].1, &env)
    });
    tests.retain(|(_, tag, _)| storages.contains_key(&tag_reads[tag]));
    if tests.is_empty() {
        return None;
    }

    // Insertions after each site, and a flag per tested (storage, case).
    let span_at =
        |site: OperationSite| func.block(site.block).operations()[site.index.as_index()].span;
    let mut edit = FunctionEdit::new(func.clone());
    let mut flags: FxHashMap<(ValueId, Ustr), ValueId> = FxHashMap::default();
    let mut inserted: FxHashMap<OperationSite, Vec<Operation>> = FxHashMap::default();
    let literal = |edit: &mut FunctionEdit, value: bool| {
        mir::Value::Constant(edit.add_constant(bool_type(), LiteralValue::new_native(value), &env))
    };
    for (site, tag, case) in &tests {
        let storage = tag_reads[tag];
        let flag = match flags.get(&(storage, *case)) {
            Some(flag) => *flag,
            None => {
                let definition = allocas[&storage].0;
                let mut alloca = Operation::alloca(span_at(definition), bool_type());
                let flag = edit.new_value();
                alloca.assign_result_id(Some(flag));
                inserted.entry(definition).or_default().push(alloca);
                for (store, stored_tag) in &storages[&storage].stores {
                    let value = literal(&mut edit, stored_tag == case);
                    inserted.entry(*store).or_default().push(Operation::store(
                        span_at(*store),
                        value,
                        mir::Value::Register(flag),
                    ));
                }
                flags.insert((storage, *case), flag);
                flag
            }
        };
        let test = &mut edit.block_mut(site.block).operations[site.index.as_index()];
        let mut load = Operation::load(test.span, mir::Value::Register(flag));
        load.assign_result_id(test.result_id());
        *test = load;
    }
    // Every use of a shadowed tag was a test, now a load.
    let unread_tags: FxHashSet<ValueId> = tests.iter().map(|(_, tag, _)| *tag).collect();
    for block in func.blocks() {
        let operations = std::mem::take(&mut edit.block_mut(block).operations);
        let mut rebuilt = Vec::with_capacity(operations.len());
        for (index, operation) in operations.into_iter().enumerate() {
            if !operation
                .result_id()
                .is_some_and(|result| unread_tags.contains(&result))
            {
                rebuilt.push(operation);
            }
            let site = OperationSite {
                block,
                index: OperationIndex::from_index(index),
            };
            if let Some(after) = inserted.remove(&site) {
                rebuilt.extend(after);
            }
        }
        edit.block_mut(block).operations = rebuilt;
    }
    Some(edit.finish_unverified())
}

impl Exit {
    fn terminator(
        self,
        span: DebugLocation,
        edit: &mut FunctionEdit,
        block: BlockId,
    ) -> Terminator {
        match self {
            Self::Goto(target) => Terminator::goto(span, target),
            Self::TestPlace {
                place,
                then_target,
                else_target,
            } => {
                // Read before replaying the join's stack cleanup. The call and its
                // result storage remain in place; only the redundant join goes.
                let condition = edit
                    .append_operation(block, Operation::load(span, mir::Value::Register(place)))
                    .expect("load has a result");
                Terminator::cond_br(span, condition, then_target, else_target)
            }
            Self::Branch {
                condition,
                then_target,
                else_target,
            } => Terminator::cond_br(
                span,
                mir::Value::Register(condition),
                then_target,
                else_target,
            ),
        }
    }
}

fn incoming_predecessors(func: &Function) -> Vec<Vec<BlockId>> {
    let mut incoming = vec![Vec::new(); func.blocks().count()];
    for predecessor in func.blocks() {
        for target in func.block(predecessor).terminator().successors() {
            incoming[target.as_index()].push(predecessor);
        }
    }
    incoming
}

fn census_uses(func: &Function, uses: &mut FxHashMap<ValueId, Uses>) -> FxHashMap<ValueId, usize> {
    let mut value_uses = FxHashMap::default();
    for block in func.blocks() {
        let basic_block = func.block(block);
        for (index, operation) in basic_block.operations().iter().enumerate() {
            let site = OperationSite {
                block,
                index: OperationIndex::from_index(index),
            };
            for (operand_index, operand) in operation.operands.iter().enumerate() {
                let mir::Value::Register(id) = operand else {
                    continue;
                };
                *value_uses.entry(*id).or_default() += 1;
                let Some(summary) = uses.get_mut(id) else {
                    continue;
                };
                match operation.kind {
                    OperationKind::Store if operand_index == 1 => {
                        let value = match &operation.operands[0] {
                            mir::Value::Register(value) => Flag::Computed(*value),
                            literal => match bool_value(func, literal) {
                                Some(value) => Flag::Literal(value),
                                None => {
                                    summary.other = true;
                                    continue;
                                }
                            },
                        };
                        summary.stores.push(Stored { block, value });
                    }
                    OperationKind::Call { ref ty, .. }
                        if dataflow::call_result_operand_index(&operation.operands, ty)
                            == Some(operand_index) =>
                    {
                        summary.stores.push(Stored {
                            block,
                            value: Flag::CallResult(*id),
                        });
                    }
                    OperationKind::CompareEqual | OperationKind::Load => summary.reads.push(site),
                    _ => summary.other = true,
                }
            }
        }
        for operand in basic_block.terminator().operands() {
            if let mir::Value::Register(id) = operand {
                *value_uses.entry(*id).or_default() += 1;
                if let Some(summary) = uses.get_mut(id) {
                    summary.other = true;
                }
            }
        }
    }
    value_uses
}

fn plan_join(
    func: &Function,
    join: BlockId,
    incoming: &[Vec<BlockId>],
    uses: &FxHashMap<ValueId, Uses>,
    value_uses: &FxHashMap<ValueId, usize>,
) -> Option<Forward> {
    let block = func.block(join);
    let TerminatorKind::CondBr {
        condition: mir::Value::Register(condition),
        then_target,
        else_target,
    } = block.terminator().kind
    else {
        return None;
    };
    let read_index = block
        .operations()
        .iter()
        .rposition(|operation| operation.result_id() == Some(condition))?;
    let read = &block.operations()[read_index];
    if !matches!(read.kind, OperationKind::CompareEqual | OperationKind::Load)
        || value_uses.get(&condition) != Some(&1)
    {
        return None;
    }
    if then_target == join || else_target == join {
        // This rewrite removes the comparison block. A self-edge would keep it reachable and run
        // the copied stack restorations once on the predecessor and again on the join.
        return None;
    }

    let (flag, expected) = read_boolean_flag(func, read)?;
    let summary = uses.get(&flag)?;
    let read_site = OperationSite {
        block: join,
        index: OperationIndex::from_index(read_index),
    };
    if summary.other || summary.reads.as_slice() != [read_site] || summary.stores.len() < 2 {
        return None;
    }

    // The join's own cleanup runs after whatever the path already replayed, exactly as it did when
    // control still passed through these blocks in order. The read itself goes with the join.
    let join_cleanup: Vec<_> = block
        .operations()
        .iter()
        .enumerate()
        .filter(|(index, _)| *index != read_index)
        .map(|(_, operation)| operation)
        .collect();
    if !join_cleanup
        .iter()
        .all(|operation| matches!(operation.kind, OperationKind::StackRestore))
    {
        return None;
    }
    let arms = reaching_stores(func, join, &summary.stores, incoming)?
        .into_iter()
        .map(|reaching| {
            let mut replay = reaching.replay;
            replay.extend(join_cleanup.iter().copied().cloned());
            let (then_target, else_target) = if expected {
                (then_target, else_target)
            } else {
                (else_target, then_target)
            };
            let exit = match reaching.value {
                Flag::Literal(true) => Exit::Goto(then_target),
                Flag::Literal(false) => Exit::Goto(else_target),
                Flag::CallResult(place) => Exit::TestPlace {
                    place,
                    then_target,
                    else_target,
                },
                Flag::Computed(condition) => Exit::Branch {
                    condition,
                    then_target,
                    else_target,
                },
            };
            Arm {
                source: reaching.source,
                exit,
                replay,
            }
        })
        .collect();

    Some(Forward { arms })
}

/// One block found by the backward walk to decide the value the join sees, with the cleanup between
/// it and the join.
struct Reaching<T> {
    source: BlockId,
    value: T,
    replay: Vec<Operation>,
}

/// What the backward walk does with one block on a path to the join.
enum Step<T> {
    /// The block leaves `T` in the storage: redirect it.
    Source(T),
    /// The block does not decide the value: walk through it to its predecessors.
    Cross,
    /// Give up on this join.
    Refuse,
}

/// The stores that reach `join`, walking back through blocks that only carry edge cleanup.
///
/// Returns `None` unless the stores found are exactly those the use census recorded for the flag:
/// that equality is what proves the walk saw every definition reaching the join, and so that
/// redirecting these blocks cannot drop one.
fn reaching_stores<T: Copy>(
    func: &Function,
    join: BlockId,
    stores: &[Stored<T>],
    incoming: &[Vec<BlockId>],
) -> Option<Vec<Reaching<T>>> {
    let found = reaching_sources(func, join, incoming, |block| {
        let mut block_stores = stores.iter().filter(|store| store.block == block);
        match (block_stores.next(), block_stores.next()) {
            (Some(store), None) => Step::Source(store.value),
            (None, _) => Step::Cross,
            (Some(_), Some(_)) => Step::Refuse,
        }
    })?;
    (found.len() == stores.len()).then_some(found)
}

/// The blocks that decide the value seen at `join`, as `step` classifies them, walking back through
/// blocks that only carry edge cleanup.
fn reaching_sources<T>(
    func: &Function,
    join: BlockId,
    incoming: &[Vec<BlockId>],
    step: impl Fn(BlockId) -> Step<T>,
) -> Option<Vec<Reaching<T>>> {
    let mut found: Vec<Reaching<T>> = Vec::new();
    let mut visited: FxHashSet<BlockId> = FxHashSet::default();
    let mut pending: Vec<(BlockId, Vec<Operation>)> = incoming[join.as_index()]
        .iter()
        .map(|predecessor| (*predecessor, Vec::new()))
        .collect();

    while let Some((block, replay)) = pending.pop() {
        // A repeat is either a cycle or two paths meeting, and both would need this block to be
        // duplicated rather than redirected. A `condbr` with both arms on the join arrives here as
        // the same predecessor twice.
        if block == join || !visited.insert(block) || visited.len() > FORWARD_BOOLEAN_BLOCKS {
            return None;
        }
        if !matches!(
            func.block(block).terminator().kind,
            TerminatorKind::Goto { .. }
        ) {
            return None;
        }

        match step(block) {
            Step::Source(value) => {
                found.push(Reaching {
                    source: block,
                    value,
                    replay,
                });
                continue;
            }
            Step::Cross => {}
            Step::Refuse => return None,
        }

        // A block on the path that does not decide the value is only passed through if it does
        // nothing an arm cannot replay. Its operations run before whatever the path below it
        // already carries.
        let operations = func.block(block).operations();
        if !operations
            .iter()
            .all(|operation| matches!(operation.kind, OperationKind::StackRestore))
        {
            return None;
        }
        let predecessors = &incoming[block.as_index()];
        if predecessors.is_empty() {
            return None;
        }
        let mut carried = operations.to_vec();
        carried.extend(replay);
        if carried.len() > FORWARD_BOOLEAN_REPLAYED_OPERATIONS {
            return None;
        }
        for predecessor in predecessors {
            pending.push((*predecessor, carried.clone()));
        }
    }

    Some(found)
}

/// The tag a block leaves in a variant storage, when every path to its end agrees on it.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ExitTag {
    /// No path reaches the block's end yet: the identity of the meet.
    Unreached,
    Known(Ustr),
    Unknown,
}

impl ExitTag {
    fn meet(self, other: Self) -> Self {
        match (self, other) {
            (Self::Unreached, tag) | (tag, Self::Unreached) => tag,
            (Self::Known(left), Self::Known(right)) if left == right => self,
            _ => Self::Unknown,
        }
    }
}

/// The tag each block leaves in a storage whose only writes are `stores`, whole statically tagged
/// shells. Payload writes keep the tag, so a block without a store leaves what all its
/// predecessors agree on.
fn exit_tags(func: &Function, stores: &[Stored<Ustr>], incoming: &[Vec<BlockId>]) -> Vec<ExitTag> {
    // Stores are listed in operation order, so the last one in a block is the one it leaves.
    let mut stored = vec![None; incoming.len()];
    for store in stores {
        stored[store.block.as_index()] = Some(store.value);
    }
    let mut tags = vec![ExitTag::Unreached; incoming.len()];
    let mut changed = true;
    while changed {
        changed = false;
        for block in func.blocks() {
            let tag = match stored[block.as_index()] {
                Some(tag) => ExitTag::Known(tag),
                None if block == func.entry() => ExitTag::Unknown,
                None => incoming[block.as_index()]
                    .iter()
                    .fold(ExitTag::Unreached, |tag, predecessor| {
                        tag.meet(tags[predecessor.as_index()])
                    }),
            };
            if tag != tags[block.as_index()] {
                tags[block.as_index()] = tag;
                changed = true;
            }
        }
    }
    tags
}

/// The flag `operation` reads, and the stored value that sends control to the `condbr`'s *then*
/// target.
///
/// A `load` yields the flag itself, so `true` takes the then edge. A `comp_eq` yields the pattern
/// it compares against, so the arm storing that pattern is the one that takes it.
fn read_boolean_flag(func: &Function, operation: &Operation) -> Option<(ValueId, bool)> {
    if matches!(operation.kind, OperationKind::Load) {
        let [mir::Value::Register(flag)] = operation.operands.as_ref() else {
            return None;
        };
        return Some((*flag, true));
    }
    let [left, right] = operation.operands.as_ref() else {
        return None;
    };
    match (left, right) {
        (mir::Value::Register(flag), literal) | (literal, mir::Value::Register(flag)) => {
            bool_value(func, literal).map(|value| (*flag, value))
        }
        _ => None,
    }
}

fn bool_value(func: &Function, value: &mir::Value) -> Option<bool> {
    let literal = match value {
        mir::Value::Constant(id) => &func.constant(*id).representation,
        mir::Value::Pattern(literal) => literal,
        _ => return None,
    };
    literal.as_primitive_ty::<bool>().copied()
}

#[cfg(test)]
mod tests {
    use ustr::ustr;

    use super::{
        bool_value, forward_boolean_branches, forward_variant_branches, shadow_variant_tag_tests,
    };
    use crate::{
        CompilerSession, Location, MirOptimization,
        containers::b,
        hir::{
            function::ArgConvention,
            value::{LiteralValue, VariantPayloadStorage},
        },
        mir::{
            Operation, OperationKind, ParameterKind, Value,
            builder::FunctionBuilder,
            terminator::{Terminator, TerminatorKind},
        },
        std::math::int_type,
        types::{
            effects::EffType,
            r#type::{CallImplType, FnType, Type},
        },
    };

    fn optimized(src: &str) -> String {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        session.emit_mir("branch_forward", src)
    }

    fn body_of<'a>(module: &'a str, name: &str) -> &'a str {
        module
            .split(&format!("fn {name}"))
            .nth(1)
            .unwrap_or_else(|| panic!("module has no `{name}`:\n{module}"))
            .split("\nfn ")
            .next()
            .unwrap()
    }

    /// An integer comparison used only for control flow dispatches on its semantic tag.
    /// Cleanup must retain that branch without materializing an intermediate boolean.
    #[test]
    fn an_integer_comparison_needs_no_materialized_boolean() {
        let module = optimized(
            "fn choose(x: int) -> int { if (match cmp(x, 10) { Less => true, _ => false }) { 1 } else { 2 } }",
        );
        let body = body_of(&module, "choose");

        assert_eq!(
            body.matches("condbr").count() + body.matches("switch_variant").count(),
            1,
            "the ordering must dispatch exactly once:\n{body}"
        );
        assert!(
            !body.contains("alloca bool"),
            "control-only comparison needs no boolean storage:\n{body}"
        );
    }

    /// A short-circuit `or` over two integer comparisons needs only their two tag tests.
    /// The composed boolean remains control flow rather than becoming a stored flag.
    #[test]
    fn short_circuit_integer_comparisons_need_no_materialized_boolean() {
        let module = optimized(
            "fn f(i: int, n: int) { if (match cmp(i, 0) { Less => true, _ => false }) or (match cmp(i, n) { Less => false, _ => true }) { 1 } else { 2 } }",
        );
        let body = body_of(&module, "f");

        assert_eq!(
            body.matches("condbr").count() + body.matches("switch_variant").count(),
            2,
            "only the two ordering dispatches must remain:\n{body}"
        );
        assert!(
            !body.contains("alloca bool"),
            "the flag holding the `or` result must be removed by DCE:\n{body}"
        );
        assert_eq!(
            body.matches("extract_tag").count(),
            2,
            "each native ordering is tested once, without a boolean retest:\n{body}"
        );
    }

    /// Native predicates return into places. Their result may be the last operand
    /// of a short-circuit expression without retaining the shared Boolean join.
    #[test]
    fn short_circuit_predicate_results_branch_at_their_calls() {
        let module =
            optimized("fn f(i: int, n: int) -> int { if i < 0 or i >= n { 1 } else { 2 } }");
        let body = body_of(&module, "f");
        assert_eq!(body.matches("condbr").count(), 2, "{body}");
        assert_eq!(body.matches("call std::lt_int").count(), 1, "{body}");
        assert_eq!(body.matches("call std::ge_int").count(), 1, "{body}");
    }

    #[test]
    fn forwarding_call_results_preserves_short_circuit_effects() {
        let source = "fn tick(n: &mut int) -> bool { n = n + 1; n == 1 }
            fn main() { let mut n = 0; let flag = black_box(true);
                if flag or tick(n) { () };
                if not flag and tick(n) { () };
                if not flag or tick(n) { () };
                n
            }";
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        assert_eq!(session.eval_mir("forward_calls", source), "1");
        session.set_mir_optimization(MirOptimization::Disabled);
        assert_eq!(session.eval_mir("raw_calls", source), "1");
    }

    #[test]
    fn a_local_trivial_variant_dispatch_is_forwarded() {
        let module = optimized(
            "fn choose(flag: bool, value: int) {\
                 if flag { Some(value) } else { None }\
             }\
             fn consume(flag: bool, value: int) -> int {\
                 match choose(flag, value) { Some(v) => v + 1, _ => 0 }\
             }",
        );
        let body = body_of(&module, "consume");

        assert!(
            !body.contains("switch_variant") && !body.contains("extract_tag"),
            "the constructor paths must select their consumers directly:\n{body}"
        );
    }

    #[test]
    fn a_nested_multiway_variant_dispatch_is_forwarded() {
        let module = optimized(
            "fn choose(first: bool, second: bool, value: int) {\
                 if first { First(value) } else if second { Second(value + 1) } else { None }\
             }\
             fn consume(first: bool, second: bool, value: int) -> int {\
                 match choose(first, second, value) {\
                     First(v) => v, Second(v) => v * 2, _ => 0\
                 }\
             }",
        );
        let body = body_of(&module, "consume");

        assert!(
            !body.contains("switch_variant") && !body.contains("extract_tag"),
            "every constructor path must select its consumer directly:\n{body}"
        );
        assert!(
            body.contains("Num<std::int>::add") && body.contains("Num<std::int>::mul"),
            "the nested constructor and selected consumers must remain:\n{body}"
        );
        assert!(
            body.contains("stack_restore"),
            "cleanup between a nested constructor and the join must be replayed:\n{body}"
        );
    }

    /// A path may store its shell before more control flow, here the diamond computing the payload,
    /// whose arms meet again before the join. The tag that path leaves still selects its consumer.
    #[test]
    fn a_variant_tag_stored_before_a_diamond_is_forwarded() {
        let module = optimized(
            "fn choose(flag: bool, wide: bool, value: int) {\
                 if flag { Some(if wide { value * 2 } else { value + 1 }) } else { None }\
             }\
             fn consume(flag: bool, wide: bool, value: int) -> int {\
                 match choose(flag, wide, value) { Some(v) => v + 3, _ => 0 }\
             }",
        );
        let body = body_of(&module, "consume");

        assert!(
            !body.contains("switch_variant") && !body.contains("extract_tag"),
            "the constructor paths must select their consumers directly:\n{body}"
        );
    }

    /// An array iterator's inlined `next` stores `Some` before its ring-buffer wrap test.
    #[test]
    fn a_for_loop_over_an_array_needs_no_tag_dispatch() {
        let module = optimized("fn sum(x: [int]) { let mut sum = 0; for a in x { sum += a }; sum }");
        let body = body_of(&module, "sum");

        assert!(
            !body.contains("switch_variant") && !body.contains("extract_tag"),
            "the loop must branch on the iterator's bound only:\n{body}"
        );
    }

    #[test]
    fn a_managed_variant_dispatch_is_not_forwarded() {
        let module = optimized(
            "fn choose(flag: bool, value: string) {\
                 if flag { Some(value) } else { None }\
             }\
             fn consume(flag: bool, value: string) -> int {\
                 match choose(flag, value) { Some(v) => string_byte_len(v), _ => 0 }\
             }",
        );
        let body = body_of(&module, "consume");

        assert_eq!(
            body.matches("switch_variant").count(),
            1,
            "managed storage retains its explicit tag dispatch:\n{body}"
        );
    }

    #[test]
    fn a_variant_payload_that_escapes_is_not_forwarded() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        let some = ustr("Some");
        let none = ustr("None");
        let payload_ty = Type::tuple([int_type()]);
        let variant_ty = Type::variant([(none, Type::unit()), (some, payload_ty)]);
        let mutator_ty =
            FnType::new_mut_resolved([(int_type(), true)], Type::unit(), EffType::empty());
        let mut builder = FunctionBuilder::new("escaped_variant".into(), Default::default());
        let mutator = builder.add_parameter(
            Type::function_type(mutator_ty.clone()),
            ParameterKind::Parameter(ArgConvention::Let),
        );
        let condition = builder.add_constant(
            Type::primitive::<bool>(),
            LiteralValue::new_native(true),
            &env,
        );
        let zero = builder.add_constant(int_type(), LiteralValue::new_native(0isize), &env);
        let entry = builder.add_block();
        let some_source = builder.add_block();
        let none_source = builder.add_block();
        let join = builder.add_block();
        let some_target = builder.add_block();
        let none_target = builder.add_block();

        let storage = builder
            .append_operation(entry, Operation::alloca(span, variant_ty))
            .unwrap();
        builder.set_terminator(
            entry,
            Terminator::cond_br(span, Value::Constant(condition), some_source, none_source),
        );

        let some_shell = builder
            .append_operation(
                some_source,
                Operation::variant(
                    span,
                    some,
                    variant_ty,
                    payload_ty,
                    Some(VariantPayloadStorage::Inline),
                    None,
                    None,
                ),
            )
            .unwrap();
        builder.append_operation(
            some_source,
            Operation::store(span, some_shell, storage.clone()),
        );
        let payload = builder
            .append_operation(
                some_source,
                Operation::variant_payload(
                    span,
                    storage.clone(),
                    Value::Constant(zero),
                    payload_ty,
                    None,
                ),
            )
            .unwrap();
        let element = builder
            .append_operation(
                some_source,
                Operation::product_subfield(
                    span,
                    payload,
                    Value::Constant(zero),
                    int_type(),
                    payload_ty,
                    [],
                ),
            )
            .unwrap();
        builder.append_operation(
            some_source,
            Operation::store(span, Value::Constant(zero), element.clone()),
        );
        let call_result = builder
            .append_operation(some_source, Operation::alloca(span, Type::unit()))
            .unwrap();
        builder.append_operation(
            some_source,
            Operation::call(
                span,
                Value::Parameter(mutator),
                [element, call_result],
                CallImplType::value(mutator_ty),
            ),
        );
        builder.set_terminator(some_source, Terminator::goto(span, join));

        let none_shell = builder
            .append_operation(
                none_source,
                Operation::variant(
                    span,
                    none,
                    variant_ty,
                    Type::unit(),
                    Some(VariantPayloadStorage::Inline),
                    None,
                    None,
                ),
            )
            .unwrap();
        builder.append_operation(
            none_source,
            Operation::store(span, none_shell, storage.clone()),
        );
        builder.set_terminator(none_source, Terminator::goto(span, join));

        let tag = builder
            .append_operation(join, Operation::extract_tag(span, storage))
            .unwrap();
        builder.set_terminator(
            join,
            Terminator::switch_variant(span, tag, vec![(some, some_target)], none_target),
        );
        builder.set_terminator(some_target, Terminator::ret(span));
        builder.set_terminator(none_target, Terminator::ret(span));

        let function = builder.finish(env);
        assert!(forward_variant_branches(&function, env).is_none());
    }

    /// A boolean alternative head lowers to `load`, so nothing in the emitter produces the
    /// comparison form of the join any more. Build it directly to keep the retained arm honest:
    /// the rewrite must still fire, and the pattern's polarity must pick the right successor —
    /// against `false`, the arm storing `false` is the one that takes the *then* edge.
    #[test]
    fn a_comparison_form_join_is_still_forwarded() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        let bool_ty = Type::primitive::<bool>();
        let mut builder = FunctionBuilder::new("comparison_join".into(), Default::default());
        let true_value = builder.add_constant(bool_ty, LiteralValue::new_native(true), &env);
        let false_value = builder.add_constant(bool_ty, LiteralValue::new_native(false), &env);
        let entry = builder.add_block();
        let left = builder.add_block();
        let right = builder.add_block();
        let join = builder.add_block();
        let yes = builder.add_block();
        let no = builder.add_block();

        let flag = builder
            .append_operation(entry, Operation::alloca(span, bool_ty))
            .unwrap();
        builder.set_terminator(
            entry,
            Terminator::cond_br(span, Value::Constant(true_value), left, right),
        );
        builder.append_operation(
            left,
            Operation::store(span, Value::Constant(true_value), flag.clone()),
        );
        builder.set_terminator(left, Terminator::goto(span, join));
        builder.append_operation(
            right,
            Operation::store(span, Value::Constant(false_value), flag.clone()),
        );
        builder.set_terminator(right, Terminator::goto(span, join));
        let comparison = builder
            .append_operation(
                join,
                Operation::compare_eq(
                    span,
                    flag,
                    Value::Pattern(b(LiteralValue::new_native(false))),
                ),
            )
            .unwrap();
        builder.set_terminator(join, Terminator::cond_br(span, comparison, yes, no));
        // Distinguishable markers, so the assertions can tell the two successors apart after the
        // rewrite has merged them into the arms that now jump straight to them.
        builder.append_operation(yes, Operation::check_fuel(span));
        builder.set_terminator(yes, Terminator::ret(span));
        builder.append_operation(no, Operation::check_call_depth(span));
        builder.set_terminator(no, Terminator::ret(span));

        let forwarded = forward_boolean_branches(&builder.finish(env))
            .expect("the comparison form must still be forwarded");
        let stored_with = |value: bool, marker: &OperationKind| {
            forwarded.blocks().any(|block| {
                let operations = forwarded.block(block).operations();
                operations.iter().any(|operation| {
                    matches!(operation.kind, OperationKind::Store)
                        && bool_value(&forwarded, &operation.operands[0]) == Some(value)
                }) && operations.iter().any(|operation| &operation.kind == marker)
            })
        };
        assert!(
            !forwarded
                .blocks()
                .flat_map(|block| forwarded.block(block).operations())
                .any(|operation| matches!(operation.kind, OperationKind::CompareEqual)),
            "the join's comparison must be gone"
        );
        assert!(
            stored_with(false, &OperationKind::CheckFuel),
            "the arm storing the compared pattern must take the then edge"
        );
        assert!(
            stored_with(true, &OperationKind::CheckCallDepth),
            "the arm storing the other value must take the else edge"
        );
    }

    /// An arm storing a computed boolean cannot pick an edge itself, but it can branch on what it
    /// stored: the join's read and branch then run on that arm alone.
    #[test]
    fn an_arm_storing_a_computed_boolean_branches_on_it() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        let bool_ty = Type::primitive::<bool>();
        let mut builder = FunctionBuilder::new("computed_join".into(), Default::default());
        let argument = builder.add_parameter(bool_ty, ParameterKind::Parameter(ArgConvention::Let));
        let true_value = builder.add_constant(bool_ty, LiteralValue::new_native(true), &env);
        let entry = builder.add_block();
        let left = builder.add_block();
        let right = builder.add_block();
        let join = builder.add_block();
        let yes = builder.add_block();
        let no = builder.add_block();

        let flag = builder
            .append_operation(entry, Operation::alloca(span, bool_ty))
            .unwrap();
        let condition = builder
            .append_operation(entry, Operation::load(span, Value::Parameter(argument)))
            .unwrap();
        builder.set_terminator(entry, Terminator::cond_br(span, condition, left, right));
        builder.append_operation(
            left,
            Operation::store(span, Value::Constant(true_value), flag.clone()),
        );
        builder.set_terminator(left, Terminator::goto(span, join));
        let computed = builder
            .append_operation(
                right,
                Operation::compare_eq(
                    span,
                    Value::Parameter(argument),
                    Value::Pattern(b(LiteralValue::new_native(false))),
                ),
            )
            .unwrap();
        builder.append_operation(
            right,
            Operation::store(span, computed.clone(), flag.clone()),
        );
        builder.set_terminator(right, Terminator::goto(span, join));
        let read = builder
            .append_operation(join, Operation::load(span, flag))
            .unwrap();
        builder.set_terminator(join, Terminator::cond_br(span, read, yes, no));
        builder.append_operation(yes, Operation::check_fuel(span));
        builder.set_terminator(yes, Terminator::ret(span));
        builder.append_operation(no, Operation::check_call_depth(span));
        builder.set_terminator(no, Terminator::ret(span));

        let forwarded = forward_boolean_branches(&builder.finish(env))
            .expect("a computed store must be threaded");
        assert!(
            !forwarded
                .blocks()
                .flat_map(|block| forwarded.block(block).operations())
                .any(|operation| matches!(operation.kind, OperationKind::Load)
                    && operation.operands[0] != Value::Parameter(argument)),
            "the join's read must be gone"
        );
        assert!(
            forwarded.blocks().any(|block| matches!(
                &forwarded.block(block).terminator().kind,
                TerminatorKind::CondBr { condition, .. } if *condition == computed
            )),
            "the computing arm must branch on its own value"
        );
    }

    /// A tag test on a local variant whose every write is a tagged shell becomes a load of a
    /// boolean each write keeps in step, so the arms store literals and the variant goes unread.
    #[test]
    fn a_tag_test_reads_a_boolean_shadow() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        let bool_ty = Type::primitive::<bool>();
        let (less, greater) = (ustr("Less"), ustr("Greater"));
        let variant_ty = Type::variant([(less, Type::unit()), (greater, Type::unit())]);
        let mut builder = FunctionBuilder::new("shadowed_tag".into(), Default::default());
        let argument = builder.add_parameter(bool_ty, ParameterKind::Parameter(ArgConvention::Let));
        let entry = builder.add_block();
        let left = builder.add_block();
        let right = builder.add_block();
        let join = builder.add_block();
        let yes = builder.add_block();
        let no = builder.add_block();

        let storage = builder
            .append_operation(entry, Operation::alloca(span, variant_ty))
            .unwrap();
        let condition = builder
            .append_operation(entry, Operation::load(span, Value::Parameter(argument)))
            .unwrap();
        builder.set_terminator(entry, Terminator::cond_br(span, condition, left, right));
        for (block, tag) in [(left, less), (right, greater)] {
            let shell = builder
                .append_operation(
                    block,
                    Operation::variant(
                        span,
                        tag,
                        variant_ty,
                        Type::unit(),
                        Some(VariantPayloadStorage::Inline),
                        None,
                        None,
                    ),
                )
                .unwrap();
            builder.append_operation(block, Operation::store(span, shell, storage.clone()));
            builder.set_terminator(block, Terminator::goto(span, join));
        }
        let tag = builder
            .append_operation(join, Operation::extract_tag(span, storage))
            .unwrap();
        let test = builder
            .append_operation(
                join,
                Operation::compare_eq(
                    span,
                    tag,
                    Value::Pattern(b(LiteralValue::new_variant_tag(less))),
                ),
            )
            .unwrap();
        builder.set_terminator(join, Terminator::cond_br(span, test, yes, no));
        builder.set_terminator(yes, Terminator::ret(span));
        builder.set_terminator(no, Terminator::ret(span));

        let shadowed = shadow_variant_tag_tests(&builder.finish(env), env)
            .expect("the tag test must read a shadow");
        let operations: Vec<_> = shadowed
            .blocks()
            .flat_map(|block| shadowed.block(block).operations())
            .collect();
        assert!(
            !operations.iter().any(|operation| matches!(
                operation.kind,
                OperationKind::ExtractTag | OperationKind::CompareEqual
            )),
            "the tag read and test must be gone"
        );
        let stored = |value: bool| {
            operations.iter().any(|operation| {
                matches!(operation.kind, OperationKind::Store)
                    && bool_value(&shadowed, &operation.operands[0]) == Some(value)
            })
        };
        assert!(
            stored(true) && stored(false),
            "each arm must store its outcome"
        );
    }

    /// Redirecting around arbitrary work in the join would silently delete it. Only stack
    /// restoration is part of the recognized edge-cleanup prefix.
    #[test]
    fn a_join_with_other_work_is_refused() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        let bool_ty = Type::primitive::<bool>();
        let mut builder = FunctionBuilder::new("other_join_work".into(), Default::default());
        let condition = builder.add_constant(bool_ty, LiteralValue::new_native(true), &env);
        let true_value = condition;
        let false_value = builder.add_constant(bool_ty, LiteralValue::new_native(false), &env);
        let entry = builder.add_block();
        let left = builder.add_block();
        let right = builder.add_block();
        let join = builder.add_block();
        let yes = builder.add_block();
        let no = builder.add_block();

        let flag = builder
            .append_operation(entry, Operation::alloca(span, bool_ty))
            .unwrap();
        builder.set_terminator(
            entry,
            Terminator::cond_br(span, Value::Constant(condition), left, right),
        );
        builder.append_operation(
            left,
            Operation::store(span, Value::Constant(true_value), flag.clone()),
        );
        builder.set_terminator(left, Terminator::goto(span, join));
        builder.append_operation(
            right,
            Operation::store(span, Value::Constant(false_value), flag.clone()),
        );
        builder.set_terminator(right, Terminator::goto(span, join));
        builder.append_operation(join, Operation::check_fuel(span));
        let comparison = builder
            .append_operation(
                join,
                Operation::compare_eq(
                    span,
                    flag,
                    Value::Pattern(b(LiteralValue::new_native(true))),
                ),
            )
            .unwrap();
        builder.set_terminator(join, Terminator::cond_br(span, comparison, yes, no));
        builder.set_terminator(yes, Terminator::ret(span));
        builder.set_terminator(no, Terminator::ret(span));

        let function = builder.finish(env);
        assert!(forward_boolean_branches(&function).is_none());
    }
}
