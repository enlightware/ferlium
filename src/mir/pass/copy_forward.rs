// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

//! Forwarding of redundant `TrivialCopy` storage.
//!
//! Value-call CSE cannot replace a repeated call's out-slot directly: expression equivalence says
//! that the values are equal, not that two mutable places may be aliased. It therefore emits the
//! universally safe `%dst = alloca; memcpy %src to %dst`. This pass performs the separate storage
//! proof and, when `%dst` has no independent identity, rewrites its reads to `%src` and removes the
//! copy and destination allocation.
//!
//! Lowering can also stage a `TrivialCopy` through a fresh local immediately before transferring it
//! into its real destination: `memcpy %source to %temporary; move %temporary to %destination`. When
//! the temporary has exactly those two uses, the memcpy can target the final destination directly
//! and both the move and temporary allocation can be removed.
//!
//! The result-slot proof is deliberately narrow and linear. Both places must be local `alloca`s in
//! the same block, with the source allocated first. Each must have exactly one whole-place write;
//! the destination's must be the candidate `memcpy`. Every other use must be a direct immutable
//! read. This excludes projections, mutable arguments, ownership transfers and other escaping uses,
//! so there is no alias through which either place can change. Allocating the source first also
//! proves it outlives the destination across every `stack_restore`.

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    hir::function::ArgConvention,
    mir::{
        self, BlockId, Function, Operation, OperationKind, edit::FunctionEdit,
        terminator::TerminatorKind, value::ValueId,
    },
    module::{ModuleEnv, id::Id},
};

use super::dataflow::call_operands;

crate::define_id_type!(
    /// A transient position in one block's operation vector, not a stable MIR identity.
    OperationIndex
);

#[derive(Clone, Copy, PartialEq, Eq)]
struct OperationSite {
    block: BlockId,
    index: OperationIndex,
}

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

struct StagedMove {
    copy_site: OperationSite,
    move_site: OperationSite,
    temporary: ValueId,
    destination: mir::Value,
}

/// Rewrites provably redundant local copies, returning `None` when there are none.
pub(crate) fn forward_trivial_copies(func: &Function, env: ModuleEnv<'_>) -> Option<Function> {
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
    let mut staged_moves = Vec::new();
    for block in func.blocks() {
        let operations = func.block(block).operations();
        for (index, pair) in operations.windows(2).enumerate() {
            let [copy, moved] = pair else { unreachable!() };
            let (
                OperationKind::Memcpy,
                [_, mir::Value::Register(temporary)],
                OperationKind::Move,
                [mir::Value::Register(move_source), destination],
            ) = (
                &copy.kind,
                copy.operands.as_ref(),
                &moved.kind,
                moved.operands.as_ref(),
            )
            else {
                continue;
            };
            let copy_site = OperationSite {
                block,
                index: OperationIndex::from_index(index),
            };
            if !definitions.contains_key(temporary) {
                continue;
            }
            // The alloca may be in a dominating block. The existing move proves its destination is
            // available at this exact point; the use census below is what removes any independent
            // path-sensitive role for the temporary.
            if temporary == move_source {
                staged_moves.push(StagedMove {
                    copy_site,
                    move_site: OperationSite {
                        block,
                        index: OperationIndex::from_index(index + 1),
                    },
                    temporary: *temporary,
                    destination: destination.clone(),
                });
            }
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
    if copies.is_empty() && staged_moves.is_empty() {
        return None;
    }

    // Only places participating in a structurally viable copy need a whole-function use census.
    let mut uses: FxHashMap<ValueId, Uses> = copies
        .iter()
        .flat_map(|copy| [copy.source, copy.destination])
        .chain(staged_moves.iter().map(|staged| staged.temporary))
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
    for staged in staged_moves {
        let temporary_uses = &uses[&staged.temporary];
        if temporary_uses.references != 2 || temporary_uses.unsafe_use {
            continue;
        }

        retargeted.push((staged.copy_site, staged.destination));
        removed
            .entry(staged.move_site.block)
            .or_default()
            .insert(staged.move_site.index);
        let definition = definitions[&staged.temporary];
        removed
            .entry(definition.site.block)
            .or_default()
            .insert(definition.site.index);
    }
    for copy in copies {
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
        edit.block_mut(site.block).operations[site.index.as_index()].operands[1] = destination;
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
    Some(edit.finish(env))
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
        CompilerSession, ExecutionTarget, MirOptimization, Path,
        hir::value::Value,
        mir::{
            operation::OperationKindDiscriminant as Op,
            profile::{MirInstructionCounts, MirInstructionKind as Kind},
        },
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

        assert!(
            body.contains("memcpy") && body.matches("alloca int").count() >= 2,
            "an independently written copy must remain a distinct place:\n{body}"
        );
    }
}
