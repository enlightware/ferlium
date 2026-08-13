// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

//! Forwarding of redundant local storage.
//!
//! Value-call CSE cannot replace a repeated call's out-slot directly: expression equivalence says
//! that the values are equal, not that two mutable places may be aliased. It therefore emits the
//! universally safe `%dst = alloca; memcpy %src to %dst`. This pass performs the separate storage
//! proof and, when `%dst` has no independent identity, rewrites its reads to `%src` and removes the
//! copy and destination allocation.
//!
//! Lowering can also initialize a fresh local immediately before transferring it into its real
//! destination: `producer ... %temporary; move %temporary to %destination`. When the temporary has
//! exactly those two uses, the producer can target the final destination directly and both the
//! transfer and temporary allocation can be removed. Producers with an explicit destination are
//! supported uniformly: `store`, `memcpy`, `move`, `clone` and `call`; the final transfer may be a
//! `move` or a `memcpy`.
//!
//! The result-slot proof is deliberately narrow and linear. Both places must be local `alloca`s in
//! the same block, with the source allocated first. Each must have exactly one whole-place write;
//! the destination's must be the candidate `memcpy`. Every other use must be a direct immutable
//! read. This excludes projections, mutable arguments, ownership transfers and other escaping uses,
//! so there is no alias through which either place can change. Allocating the source first also
//! proves it outlives the destination across every `stack_restore`.

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    containers::SVec2,
    hir::function::ArgConvention,
    mir::{
        self, BlockId, Function, Operation, OperationKind, edit::FunctionEdit,
        terminator::TerminatorKind, value::ValueId,
    },
    module::{ModuleEnv, id::Id},
    types::type_properties::concrete_type_is_trivial_copy,
};

use super::dataflow::{call_operands, field_index};

use super::site::{OperationIndex, OperationSite};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Site {
    Operation(OperationSite),
    Terminator(BlockId),
}

#[derive(Clone, Copy)]
struct Definition {
    site: OperationSite,
}

#[derive(Default)]
struct Uses {
    references: usize,
    writes: usize,
    sole_write: Option<Site>,
    unsafe_use: bool,
}

impl Uses {
    fn read(&mut self) {
        self.references += 1;
    }

    fn write(&mut self, site: Site) {
        self.references += 1;
        self.writes += 1;
        self.sole_write = (self.writes == 1).then_some(site);
    }

    fn unsafe_use(&mut self) {
        self.references += 1;
        self.unsafe_use = true;
    }

    fn is_stable(&self) -> bool {
        self.writes == 1 && !self.unsafe_use
    }
}

#[derive(Clone, Copy)]
struct Copy {
    site: OperationSite,
    source: ValueId,
    destination: ValueId,
}

struct ForwardedInitialization {
    producer_site: OperationSite,
    transfer_site: OperationSite,
    temporary: ValueId,
    destination: mir::Value,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum PlaceRoot {
    Constant(mir::value::ConstantId),
    Parameter(mir::value::ParameterId),
    Result(ValueId),
}

#[derive(Clone, PartialEq, Eq)]
struct PlaceIdentity {
    root: PlaceRoot,
    fields: SVec2<usize>,
}

#[derive(Clone)]
enum OperandStorage {
    None,
    Place(PlaceIdentity),
    Unknown,
}

/// Rewrites provably redundant local storage, returning `None` when there is none.
pub(crate) fn forward_redundant_storage(func: &Function, env: ModuleEnv<'_>) -> Option<Function> {
    let mut definitions = FxHashMap::default();
    let mut copies = Vec::new();
    for block in func.blocks() {
        for (index, operation) in func.block(block).operations().iter().enumerate() {
            let site = OperationSite {
                block,
                index: OperationIndex::from_index(index),
            };
            if matches!(operation.kind, OperationKind::Alloca { .. })
                && let Some(result) = operation.result_id()
            {
                definitions.insert(result, Definition { site });
            } else if matches!(operation.kind, OperationKind::Memcpy)
                && let [
                    mir::Value::Register(source),
                    mir::Value::Register(destination),
                ] = operation.operands.as_ref()
            {
                copies.push(Copy {
                    site,
                    source: *source,
                    destination: *destination,
                });
            }
        }
    }
    let mut forwarded_initializations = Vec::new();
    for block in func.blocks() {
        let operations = func.block(block).operations();
        for (index, pair) in operations.windows(2).enumerate() {
            let [producer, transfer] = pair else {
                unreachable!()
            };
            if !matches!(transfer.kind, OperationKind::Move | OperationKind::Memcpy) {
                continue;
            }
            let [mir::Value::Register(transfer_source), destination, ..] =
                transfer.operands.as_ref()
            else {
                continue;
            };
            let Some(destination_index) = initialization_destination_index(producer) else {
                continue;
            };
            let mir::Value::Register(temporary) = &producer.operands[destination_index] else {
                continue;
            };
            if temporary != transfer_source || !definitions.contains_key(temporary) {
                continue;
            }
            let producer_site = OperationSite {
                block,
                index: OperationIndex::from_index(index),
            };
            // The alloca may be in a dominating block. The existing transfer proves its final
            // destination is available at this exact point; the use census below is what removes
            // any independent path-sensitive role for the temporary.
            forwarded_initializations.push(ForwardedInitialization {
                producer_site,
                transfer_site: OperationSite {
                    block,
                    index: OperationIndex::from_index(index + 1),
                },
                temporary: *temporary,
                destination: destination.clone(),
            });
        }
    }
    // Keeping all three operations in one block makes allocation order a lifetime proof: the
    // earlier source cannot be popped while the later destination remains live.
    copies.retain(|copy| {
        let Some(source) = definitions.get(&copy.source) else {
            return false;
        };
        let Some(destination) = definitions.get(&copy.destination) else {
            return false;
        };
        source.site.block == copy.site.block
            && destination.site.block == copy.site.block
            && source.site.index.as_u32() < destination.site.index.as_u32()
            && destination.site.index.as_u32() < copy.site.index.as_u32()
    });
    if copies.is_empty() && forwarded_initializations.is_empty() {
        return None;
    }
    // Place identities are only needed by initialization retargeting. Avoid indexing every result
    // in rounds whose structural scan found only the original CSE-copy forwarding candidates.
    let operation_definitions: FxHashMap<_, _> = if forwarded_initializations.is_empty() {
        FxHashMap::default()
    } else {
        func.blocks()
            .flat_map(|block| func.block(block).operations())
            .filter_map(|operation| operation.result_id().map(|result| (result, operation)))
            .collect()
    };

    // Only places participating in a structurally viable copy need a whole-function use census.
    let mut uses: FxHashMap<ValueId, Uses> = copies
        .iter()
        .flat_map(|copy| [copy.source, copy.destination])
        .chain(
            forwarded_initializations
                .iter()
                .map(|forwarded| forwarded.temporary),
        )
        .map(|id| (id, Uses::default()))
        .collect();
    for block in func.blocks() {
        let basic_block = func.block(block);
        for (index, operation) in basic_block.operations().iter().enumerate() {
            let site = OperationSite {
                block,
                index: OperationIndex::from_index(index),
            };
            note_operation(operation, Site::Operation(site), &mut uses);
        }
        if let TerminatorKind::Invoke { operation, .. } = &basic_block.terminator().kind {
            note_operation(operation, Site::Terminator(block), &mut uses);
        }
        match &basic_block.terminator().kind {
            TerminatorKind::CondBr { condition, .. } => note_unsafe(condition, &mut uses),
            TerminatorKind::Yield { place, .. } => note_unsafe(place, &mut uses),
            TerminatorKind::Goto { .. }
            | TerminatorKind::Invoke { .. }
            | TerminatorKind::Return
            | TerminatorKind::PropagateError
            | TerminatorKind::FailureDuringCleanup => {}
        }
    }

    let mut replacements: FxHashMap<ValueId, ValueId> = FxHashMap::default();
    let mut removed: FxHashMap<BlockId, FxHashSet<OperationIndex>> = FxHashMap::default();
    let mut retargeted = Vec::new();
    let forwarded_initializations: Vec<_> = forwarded_initializations
        .into_iter()
        .filter(|forwarded| {
            let temporary_uses = &uses[&forwarded.temporary];
            temporary_uses.references == 2 && !temporary_uses.unsafe_use
        })
        .collect();
    let producer_to_forwarding: FxHashMap<_, _> = forwarded_initializations
        .iter()
        .enumerate()
        .map(|(index, forwarded)| (forwarded.producer_site, index))
        .collect();
    let mut consumed = FxHashSet::default();
    let mut blocked = FxHashSet::default();
    let mut forwarded_temporaries = FxHashSet::default();
    let mut storage_cache = FxHashMap::default();
    for start in 0..forwarded_initializations.len() {
        if consumed.contains(&start) || blocked.contains(&start) {
            continue;
        }
        let first = &forwarded_initializations[start];
        let producer = operation_at(func, first.producer_site);
        let mut current = start;
        let mut last_safe = None;
        loop {
            let forwarded = &forwarded_initializations[current];
            if !can_retarget_initialization(
                producer,
                &forwarded.destination,
                func,
                &operation_definitions,
                &mut storage_cache,
                env,
            ) {
                break;
            }
            last_safe = Some(current);
            let Some(next) = producer_to_forwarding
                .get(&forwarded.transfer_site)
                .copied()
            else {
                break;
            };
            current = next;
        }
        let Some(last_safe) = last_safe else {
            continue;
        };

        retargeted.push((
            first.producer_site,
            forwarded_initializations[last_safe].destination.clone(),
        ));
        let mut current = start;
        loop {
            let forwarded = &forwarded_initializations[current];
            consumed.insert(current);
            forwarded_temporaries.insert(forwarded.temporary);
            removed
                .entry(forwarded.transfer_site.block)
                .or_default()
                .insert(forwarded.transfer_site.index);
            let definition = definitions[&forwarded.temporary];
            removed
                .entry(definition.site.block)
                .or_default()
                .insert(definition.site.index);
            if current == last_safe {
                if let Some(next) = producer_to_forwarding
                    .get(&forwarded.transfer_site)
                    .copied()
                {
                    // This producer operation is being removed as the transfer above. If the root
                    // producer could not safely target the following destination, that following
                    // candidate cannot be applied independently to the removed operation.
                    blocked.insert(next);
                }
                break;
            }
            current = producer_to_forwarding[&forwarded.transfer_site];
        }
    }
    for copy in copies {
        if forwarded_temporaries.contains(&copy.destination) {
            continue;
        }
        let destination_definition = definitions[&copy.destination];
        let source_uses = &uses[&copy.source];
        let destination_uses = &uses[&copy.destination];
        if !source_uses.is_stable()
            || !destination_uses.is_stable()
            || destination_uses.sole_write != Some(Site::Operation(copy.site))
        {
            continue;
        }

        // Copies are encountered in execution order. A source already forwarded by an earlier
        // copy therefore names its final representative directly, keeping chains linear.
        let source = replacements
            .get(&copy.source)
            .copied()
            .unwrap_or(copy.source);
        replacements.insert(copy.destination, source);
        removed
            .entry(copy.site.block)
            .or_default()
            .insert(copy.site.index);
        removed
            .entry(destination_definition.site.block)
            .or_default()
            .insert(destination_definition.site.index);
    }
    if replacements.is_empty() && retargeted.is_empty() {
        return None;
    }

    let mut edit = FunctionEdit::new(func.clone());
    for (site, destination) in retargeted {
        let producer = &mut edit.block_mut(site.block).operations[site.index.as_index()];
        let destination_index = initialization_destination_index(producer)
            .expect("a selected initialization producer must retain its destination");
        producer.operands[destination_index] = destination;
    }
    edit.visit_operands_mut(|operand| {
        if let mir::Value::Register(id) = operand
            && let Some(representative) = replacements.get(id)
        {
            *id = *representative;
        }
    });
    for (block, indices) in removed {
        let mut index = 0;
        edit.block_mut(block).operations.retain(|_| {
            let keep = !indices.contains(&OperationIndex::from_index(index));
            index += 1;
            keep
        });
    }
    Some(edit.finish_unverified())
}

fn initialization_destination_index(operation: &Operation) -> Option<usize> {
    match operation.kind {
        OperationKind::Store
        | OperationKind::Memcpy
        | OperationKind::Move
        | OperationKind::Clone { .. } => Some(1),
        OperationKind::Call { .. } => operation.operands.len().checked_sub(1),
        _ => None,
    }
}

fn operation_at(func: &Function, site: OperationSite) -> &Operation {
    &func.block(site.block).operations()[site.index.as_index()]
}

fn can_retarget_initialization(
    producer: &Operation,
    destination: &mir::Value,
    func: &Function,
    definitions: &FxHashMap<ValueId, &Operation>,
    storage_cache: &mut FxHashMap<ValueId, OperandStorage>,
    env: ModuleEnv<'_>,
) -> bool {
    let Some(destination_index) = initialization_destination_index(producer) else {
        return false;
    };
    if matches!(
        producer.kind,
        OperationKind::Call { .. } | OperationKind::Clone { .. }
    ) {
        let callee_index = if matches!(producer.kind, OperationKind::Call { .. }) {
            0
        } else {
            2
        };
        if initialization_is_trivial_copy(producer, env)
            && resolved_callee_is_native(&producer.operands[callee_index], env)
        {
            // Native calls first compute an owned HIR result and only then store it through the MIR
            // return place. Retargeting therefore cannot clobber an aliased input while it is read.
            return true;
        }
    }

    producer
        .operands
        .iter()
        .enumerate()
        .filter(|(index, _)| *index != destination_index)
        .all(|(_, input)| {
            operands_are_disjoint(input, destination, func, definitions, storage_cache)
        })
}

fn initialization_is_trivial_copy(producer: &Operation, env: ModuleEnv<'_>) -> bool {
    let ty = match &producer.kind {
        OperationKind::Call { ty, .. } => ty.ret(),
        OperationKind::Clone { ty } => *ty,
        _ => return false,
    };
    concrete_type_is_trivial_copy(ty, &env)
}

fn resolved_callee_is_native(callee: &mir::Value, env: ModuleEnv<'_>) -> bool {
    let mir::Value::Function(id) = callee else {
        return false;
    };
    let module = if id.module == env.current.module_id() {
        Some(env.current)
    } else {
        env.modules.get(id.module).and_then(|entry| entry.module())
    };
    module
        .and_then(|module| module.get_function_by_id(id.function))
        .is_some_and(|function| function.code.as_script().is_none())
}

fn operands_are_disjoint(
    first: &mir::Value,
    second: &mir::Value,
    func: &Function,
    definitions: &FxHashMap<ValueId, &Operation>,
    storage_cache: &mut FxHashMap<ValueId, OperandStorage>,
) -> bool {
    match (
        operand_storage(first, func, definitions, storage_cache),
        operand_storage(second, func, definitions, storage_cache),
    ) {
        (OperandStorage::None, _) | (_, OperandStorage::None) => true,
        (OperandStorage::Place(first), OperandStorage::Place(second)) => {
            if first.root != second.root {
                return true;
            }
            first
                .fields
                .iter()
                .zip(&second.fields)
                .any(|(first, second)| first != second)
        }
        (OperandStorage::Unknown, _) | (_, OperandStorage::Unknown) => false,
    }
}

fn operand_storage(
    operand: &mir::Value,
    func: &Function,
    definitions: &FxHashMap<ValueId, &Operation>,
    cache: &mut FxHashMap<ValueId, OperandStorage>,
) -> OperandStorage {
    match operand {
        mir::Value::Constant(id) => OperandStorage::Place(PlaceIdentity {
            root: PlaceRoot::Constant(*id),
            fields: SVec2::new(),
        }),
        mir::Value::Parameter(id) => OperandStorage::Place(PlaceIdentity {
            root: PlaceRoot::Parameter(*id),
            fields: SVec2::new(),
        }),
        mir::Value::Register(id) => {
            if let Some(storage) = cache.get(id) {
                return storage.clone();
            }
            let storage = match definitions.get(id).map(|operation| &operation.kind) {
                Some(OperationKind::Subfield { .. }) => {
                    let operation = definitions[id];
                    match (
                        operand_storage(&operation.operands[0], func, definitions, cache),
                        field_index(&operation.operands[1], func),
                    ) {
                        (OperandStorage::Place(mut place), Some(field)) => {
                            place.fields.push(field);
                            OperandStorage::Place(place)
                        }
                        _ => OperandStorage::Unknown,
                    }
                }
                // A projection exposes storage owned by one of its arguments, but its provenance
                // is not encoded directly in this operation. Reject it rather than guess.
                Some(OperationKind::Project { .. }) | None => OperandStorage::Unknown,
                Some(_) => OperandStorage::Place(PlaceIdentity {
                    root: PlaceRoot::Result(*id),
                    fields: SVec2::new(),
                }),
            };
            cache.insert(*id, storage.clone());
            storage
        }
        mir::Value::Function(_)
        | mir::Value::Dictionary(_)
        | mir::Value::Subscript(_)
        | mir::Value::Pattern(_) => OperandStorage::None,
    }
}

fn note_operation(operation: &Operation, site: Site, uses: &mut FxHashMap<ValueId, Uses>) {
    let read = |operand: &mir::Value, uses: &mut FxHashMap<ValueId, Uses>| {
        if let mir::Value::Register(id) = operand
            && let Some(summary) = uses.get_mut(id)
        {
            summary.read();
        }
    };
    let write = |operand: &mir::Value, uses: &mut FxHashMap<ValueId, Uses>| {
        if let mir::Value::Register(id) = operand
            && let Some(summary) = uses.get_mut(id)
        {
            summary.write(site);
        }
    };
    let unsafe_use = |operand: &mir::Value, uses: &mut FxHashMap<ValueId, Uses>| {
        if let mir::Value::Register(id) = operand
            && let Some(summary) = uses.get_mut(id)
        {
            summary.unsafe_use();
        }
    };

    match &operation.kind {
        OperationKind::Call { ty, .. } => {
            let Some(call) = call_operands(&operation.operands, ty) else {
                operation
                    .operands
                    .iter()
                    .for_each(|operand| unsafe_use(operand, uses));
                return;
            };
            unsafe_use(call.callee, uses);
            call.extras
                .iter()
                .for_each(|operand| unsafe_use(operand, uses));
            for (argument, convention) in call.arguments {
                match convention {
                    ArgConvention::Let => read(argument, uses),
                    ArgConvention::MutableRef => write(argument, uses),
                }
            }
            write(call.result, uses);
        }
        OperationKind::Load | OperationKind::CompareEqual | OperationKind::ExtractTag => {
            operation
                .operands
                .iter()
                .for_each(|operand| read(operand, uses));
        }
        OperationKind::Store => {
            unsafe_use(&operation.operands[0], uses);
            write(&operation.operands[1], uses);
        }
        OperationKind::BuildArray { .. } => {
            let (destination, elements) = operation
                .operands
                .split_last()
                .expect("build_array has a trailing destination");
            elements.iter().for_each(|operand| read(operand, uses));
            write(destination, uses);
        }
        OperationKind::Clear => write(&operation.operands[0], uses),
        OperationKind::Memcpy => {
            read(&operation.operands[0], uses);
            write(&operation.operands[1], uses);
        }
        OperationKind::Move => {
            write(&operation.operands[0], uses);
            write(&operation.operands[1], uses);
            operation
                .operands
                .iter()
                .skip(2)
                .for_each(|operand| unsafe_use(operand, uses));
        }
        OperationKind::Clone { .. } => {
            read(&operation.operands[0], uses);
            write(&operation.operands[1], uses);
            unsafe_use(&operation.operands[2], uses);
        }
        OperationKind::Drop { .. } => {
            write(&operation.operands[0], uses);
            operation
                .operands
                .iter()
                .skip(1)
                .for_each(|operand| unsafe_use(operand, uses));
        }
        OperationKind::DropClosureEnv => write(&operation.operands[0], uses),
        OperationKind::Alloca { .. }
        | OperationKind::Project { .. }
        | OperationKind::EndProject
        | OperationKind::Subfield { .. }
        | OperationKind::DictEntry { .. }
        | OperationKind::SubscriptMember { .. }
        | OperationKind::BuildSubscript { .. }
        | OperationKind::Variant { .. }
        | OperationKind::BuildClosure { .. }
        | OperationKind::CloneClosureEnv { .. } => operation
            .operands
            .iter()
            .for_each(|operand| unsafe_use(operand, uses)),
        OperationKind::AllocaPlace { .. }
        | OperationKind::StackSave
        | OperationKind::StackRestore
        | OperationKind::CheckCallDepth
        | OperationKind::CheckFuel => {}
    }
}

fn note_unsafe(operand: &mir::Value, uses: &mut FxHashMap<ValueId, Uses>) {
    if let mir::Value::Register(id) = operand
        && let Some(summary) = uses.get_mut(id)
    {
        summary.unsafe_use();
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        CompilerSession, ExecutionTarget, Location, MirOptimization, Path,
        format::FormatWith,
        hir::{function::ArgConvention, value::Value},
        mir::{
            self, Operation, ParameterKind,
            builder::FunctionBuilder,
            operation::OperationKindDiscriminant as Op,
            profile::{MirInstructionCounts, MirInstructionKind as Kind},
            terminator::Terminator,
        },
        module::ModuleEnv,
        std::{math::int_type, string::string_type},
    };

    fn optimized(src: &str) -> String {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        session.emit_mir("copy_forward", src)
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

    fn profile_repeated(optimization: MirOptimization) -> MirInstructionCounts {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(optimization);
        let module_id = session
            .compile_for(
                ExecutionTarget::Mir,
                "fn repeated(x: int, y: int) -> int { (x - y) * (x - y) }",
                "copy_forward_profile",
                Path::single_str("copy_forward_profile"),
            )
            .unwrap()
            .module_id;
        let entry = session
            .expect_fresh_module(module_id)
            .get_local_function_id(crate::ustr("repeated"))
            .unwrap();
        let (result, profile) = session
            .run_mir_entry_profiled(
                module_id,
                entry,
                vec![Value::native(9isize), Value::native(4isize)],
            )
            .unwrap();
        assert_eq!(result.into_primitive_ty::<isize>().unwrap(), 25);
        profile.total().clone()
    }

    fn forwarded_move_chain(env: ModuleEnv<'_>) -> crate::mir::Function {
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new("move_chain".into(), Default::default());
        let result = builder.add_parameter(int_type(), ParameterKind::Return);
        let block = builder.add_block();
        let source = builder
            .append_operation(block, Operation::alloca(span, int_type()))
            .unwrap();
        let first = builder
            .append_operation(block, Operation::alloca(span, int_type()))
            .unwrap();
        let second = builder
            .append_operation(block, Operation::alloca(span, int_type()))
            .unwrap();
        let constant = builder.add_constant(
            int_type(),
            crate::hir::value::LiteralValue::new_native(1isize),
            &env,
        );
        builder.append_operation(
            block,
            Operation::store(span, mir::Value::Constant(constant), source.clone()),
        );
        builder.append_operation(block, Operation::move_value(span, source, first.clone()));
        builder.append_operation(block, Operation::move_value(span, first, second.clone()));
        builder.append_operation(
            block,
            Operation::move_value(span, second, mir::Value::Parameter(result)),
        );
        builder.set_terminator(block, Terminator::ret(span));
        builder.finish(env)
    }

    fn staged_memcpy(env: ModuleEnv<'_>) -> crate::mir::Function {
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new("staged_memcpy".into(), Default::default());
        let source =
            builder.add_parameter(int_type(), ParameterKind::Parameter(ArgConvention::Let));
        let result = builder.add_parameter(int_type(), ParameterKind::Return);
        let block = builder.add_block();
        let temporary = builder
            .append_operation(block, Operation::alloca(span, int_type()))
            .unwrap();
        builder.append_operation(
            block,
            Operation::memcpy(span, mir::Value::Parameter(source), temporary.clone()),
        );
        builder.append_operation(
            block,
            Operation::memcpy(span, temporary, mir::Value::Parameter(result)),
        );
        builder.set_terminator(block, Terminator::ret(span));
        builder.finish(env)
    }

    #[test]
    fn a_repeated_trivial_call_reuses_the_first_result_place() {
        let module = optimized("fn repeated(x: int, y: int) -> int { (x - y) * (x - y) }");
        let body = body_of(&module, "repeated");

        assert_eq!(
            body.matches("Num<std::int>::sub").count(),
            1,
            "call CSE must compute the subtraction once:\n{body}"
        );
        assert!(
            !body.contains("memcpy"),
            "copy forwarding must reuse its result place directly:\n{body}"
        );
    }

    #[test]
    fn a_repeated_trivial_call_executes_less_optimized_mir() {
        let raw = profile_repeated(MirOptimization::Disabled);
        let optimized = profile_repeated(MirOptimization::Enabled);

        assert!(
            optimized.total() < raw.total(),
            "the optimized repeated call must execute less MIR: raw {}, optimized {}",
            raw.total(),
            optimized.total()
        );
        assert!(
            optimized.get(Kind::Operation(Op::Alloca)) < raw.get(Kind::Operation(Op::Alloca)),
            "copy forwarding must avoid executing the redundant result allocation"
        );
    }

    #[test]
    fn a_copy_immediately_moved_to_its_destination_skips_staging_storage() {
        let module = optimized("[1] |> map(|x| x)");
        let lines: Vec<_> = module.lines().map(str::trim).collect();
        let staged = lines.windows(2).any(|pair| {
            let Some((_, temporary)) = pair[0]
                .strip_prefix("memcpy ")
                .and_then(|copy| copy.split_once(" to "))
            else {
                return false;
            };
            pair[1]
                .strip_prefix("move ")
                .and_then(|moved| moved.split_once(" to "))
                .is_some_and(|(source, _)| source == temporary)
        });

        assert!(
            !staged,
            "a trivial copy must target the final move destination directly:\n{module}"
        );
    }

    #[test]
    fn a_native_call_result_is_written_back_in_place() {
        let module = optimized("fn increment(mut x: int) -> int { x = x + 1; x }");
        let body = body_of(&module, "increment");
        let add = body
            .lines()
            .find(|line| line.contains("Num<std::int>::add"))
            .unwrap_or_else(|| panic!("increment has no add call:\n{body}"));
        let arguments: Vec<_> = add
            .split_once('(')
            .unwrap()
            .1
            .trim_end_matches(')')
            .split(", ")
            .collect();

        assert_eq!(
            arguments.first(),
            arguments.last(),
            "native add must write directly to the left-hand side:\n{body}"
        );
    }

    #[test]
    fn a_stored_value_is_written_directly_to_its_assignment_destination() {
        let module = optimized("fn replace(mut x: int) -> int { x = 1; x }");
        let body = body_of(&module, "replace");

        assert_eq!(body.matches("alloca int").count(), 1, "{body}");
        assert!(
            body.lines()
                .any(|line| line.trim().starts_with("store @c0 to %r0")),
            "the constant must be stored directly into the mutable local:\n{body}"
        );
    }

    #[test]
    fn a_chain_of_moves_is_collapsed_in_one_linear_sweep() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let source = forwarded_move_chain(env);
        let forwarded = super::forward_redundant_storage(&source, env)
            .expect("the move chain must be forwarded");
        let body = forwarded.format_with(&env).to_string();

        assert_eq!(body.matches("alloca int").count(), 0, "{body}");
        assert_eq!(body.matches("move ").count(), 0, "{body}");
        assert!(body.contains("store @c0 to %p0"), "{body}");
    }

    #[test]
    fn a_memcpy_followed_by_a_final_memcpy_is_forwarded_once() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let source = staged_memcpy(env);
        let forwarded = super::forward_redundant_storage(&source, env)
            .expect("the staging memcpy must be forwarded");
        let body = forwarded.format_with(&env).to_string();

        assert_eq!(body.matches("alloca int").count(), 0, "{body}");
        assert_eq!(body.matches("memcpy ").count(), 1, "{body}");
        assert!(body.contains("memcpy %p0 to %p1"), "{body}");
    }

    #[test]
    fn a_clone_is_forwarded_to_its_final_destination() {
        let mut session = CompilerSession::new();
        let module_id = session
            .compile_for(
                ExecutionTarget::Mir,
                "fn copy(x: string) -> string { x }",
                "copy_forward_clone",
                Path::single_str("copy_forward_clone"),
            )
            .unwrap()
            .module_id;
        let module = session.expect_fresh_module(module_id);
        let copy = module.get_local_function_id(crate::ustr("copy")).unwrap();
        let raw = session
            .mir_artifacts_for(module_id, MirOptimization::Disabled)
            .unwrap()
            .get(copy)
            .unwrap();
        let clone = raw
            .blocks()
            .flat_map(|block| raw.block(block).operations())
            .find(|operation| matches!(operation.kind, mir::OperationKind::Clone { .. }))
            .expect("copying a string must use Value::clone");
        let callee = clone.operands[2].clone();
        let env = session.modules().env_for(module);
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new("staged_clone".into(), Default::default());
        let source =
            builder.add_parameter(string_type(), ParameterKind::Parameter(ArgConvention::Let));
        let result = builder.add_parameter(string_type(), ParameterKind::Return);
        let block = builder.add_block();
        let temporary = builder
            .append_operation(block, Operation::alloca(span, string_type()))
            .unwrap();
        builder.append_operation(
            block,
            Operation::clone_value(
                span,
                mir::Value::Parameter(source),
                temporary.clone(),
                callee,
                string_type(),
            ),
        );
        builder.append_operation(
            block,
            Operation::move_value(span, temporary, mir::Value::Parameter(result)),
        );
        builder.set_terminator(block, Terminator::ret(span));
        let staged = builder.finish(env);
        let forwarded = super::forward_redundant_storage(&staged, env)
            .expect("the staged clone must be forwarded");
        let body = forwarded.format_with(&env).to_string();

        assert_eq!(body.matches("alloca string").count(), 0, "{body}");
        assert_eq!(body.matches("move ").count(), 0, "{body}");
        assert!(body.contains("clone string %p0 to %p1"), "{body}");
    }

    #[test]
    fn a_script_call_result_does_not_overwrite_its_aliased_argument() {
        let module = optimized(
            "fn recursive(x: int) -> int {\n\
                 if x == 0 { 0 } else { recursive(x - 1) }\n\
             }\n\
             fn update(mut x: int) -> int { x = recursive(x); x }",
        );
        let body = body_of(&module, "update");
        let lines: Vec<_> = body.lines().map(str::trim).collect();

        assert!(
            lines.windows(2).any(|pair| {
                pair[0].contains("call copy_forward::recursive") && pair[1].starts_with("move ")
            }),
            "a script call must retain fresh result storage when its result aliases an input:\n{body}"
        );
    }

    #[test]
    fn a_script_call_can_write_to_a_sibling_field() {
        let module = optimized(
            "struct Pair { a: int, b: int }\n\
             fn recursive(x: int) -> int {\n\
                 if x == 0 { 0 } else { recursive(x - 1) }\n\
             }\n\
             fn update(mut pair: Pair) -> Pair {\n\
                 pair.b = recursive(pair.a);\n\
                 pair\n\
             }",
        );
        let body = body_of(&module, "update");
        let lines: Vec<_> = body.lines().map(str::trim).collect();
        let call = lines
            .iter()
            .position(|line| line.contains("call copy_forward::recursive"))
            .expect("update must retain its recursive call");

        assert!(
            !lines[call + 1].starts_with("move "),
            "different constant fields of one root are disjoint:\n{body}"
        );
        assert_eq!(body.matches("alloca int").count(), 0, "{body}");
    }

    #[test]
    fn a_snapshot_is_not_forwarded_across_a_source_write() {
        let module = optimized(
            "fn preserve(mut source: int, replacement: int) -> int {\n\
                 let snapshot = source;\n\
                 source = replacement;\n\
                 snapshot\n\
             }",
        );
        let body = body_of(&module, "preserve");

        assert!(
            body.contains("memcpy") && body.matches("alloca int").count() >= 2,
            "the independent snapshot must retain its own storage:\n{body}"
        );
    }

    #[test]
    fn a_copy_with_an_independent_write_keeps_its_storage() {
        let module = optimized(
            "fn change_copy(source: int, increment: int) -> int {\n\
                 let mut copy = source;\n\
                 copy = copy + increment;\n\
                 source + copy\n\
             }",
        );
        let body = body_of(&module, "change_copy");

        let copied_local = body
            .lines()
            .find_map(|line| line.trim().strip_prefix("memcpy %p0 to "))
            .expect("the source snapshot must remain");
        let add_arguments: Vec<Vec<_>> = body
            .lines()
            .filter(|line| line.contains("Num<std::int>::add"))
            .map(|line| {
                line.split_once('(')
                    .unwrap()
                    .1
                    .trim_end_matches(')')
                    .split(", ")
                    .collect()
            })
            .collect();
        assert!(
            add_arguments
                == [
                    vec![copied_local, "%p1", copied_local],
                    vec!["%p0", copied_local, "%p2"],
                ],
            "an independently written copy must remain a distinct place:\n{body}"
        );
    }
}
