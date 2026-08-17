// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

//! Hoisting of loop-invariant pure calls.
//!
//! An empty effect row excludes source-level effects and failure, while a separate `will_return`
//! proof excludes divergence when the call moves onto a zero-trip path. The pass admits any direct
//! call under those generic contracts with a concrete `TrivialCopy` value result.
//!
//! The first implementation is deliberately narrow but generic over those calls. It recognizes
//! natural loops from dominance backedges, requires one unconditional preheader, and moves a call
//! only when every input place is defined before that preheader and its storage root is unchanged
//! throughout the loop. The result must be a whole local `alloca`; no other write may reach it and
//! every use of its root must stay in the loop. When that allocation is loop-local it moves with
//! the call.
//!
//! Stack regions are part of correctness, not cleanup decoration. A loop-local result moved after a
//! preheader's `stack_save` would be popped by the matching per-iteration `stack_restore`. The
//! insertion point is therefore before every outside-loop marker restored inside the loop. A marker
//! defined before the preheader leaves no safe insertion point, and the candidate is rejected.
//!
//! The pass adds no operation and clones no expression: it only relocates an existing call and,
//! when necessary, its allocation. Acyclic bodies return before scanning calls, and bodies without
//! an eligible call return before CFG or dominance construction, keeping the corpus-wide cost
//! proportional to actual candidates.

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    hir::function::ArgConvention,
    mir::{
        self, BlockId, Function, Operation, OperationKind, dominance::Dominance,
        edit::FunctionEdit, terminator::TerminatorKind, value::ValueId,
    },
    module::{FunctionId, ModuleEnv, id::Id},
    types::{r#type::CallResultConvention, type_properties::concrete_type_is_trivial_copy},
};

use super::{
    dataflow::{self, Root},
    site::{OperationIndex, OperationSite},
};

#[derive(Clone)]
struct NaturalLoop {
    blocks: FxHashSet<BlockId>,
    preheader: BlockId,
}

#[derive(Clone, Copy)]
struct Alloca {
    site: OperationSite,
    ty: crate::types::r#type::Type,
    is_static: bool,
}

#[derive(Clone, Copy)]
struct Hoist {
    call: OperationSite,
    alloca: Option<OperationSite>,
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

/// Hoists every call admitted by the narrow LICM contract, returning `None` when nothing moved.
///
/// One candidate is moved per analysis. This keeps edits simple and lets a call hoisted from an
/// inner loop become a candidate for an enclosing loop on the next iteration. Every successful
/// iteration moves a call across at least one loop boundary, so loop nesting bounds the repeats.
pub(crate) fn hoist_loop_invariant_calls(
    func: &Function,
    env: ModuleEnv<'_>,
    will_return: &impl Fn(FunctionId) -> bool,
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
    let has_eligible_call = func.blocks().any(|block| {
        func.block(block)
            .operations()
            .iter()
            .any(|operation| eligible_call(operation, env, will_return).is_some())
    });
    if !has_eligible_call {
        return None;
    }

    let mut current: Option<Function> = None;
    loop {
        let source = current.as_ref().unwrap_or(func);
        let Some(hoist) = find_hoist(source, env, will_return) else {
            break;
        };
        current = Some(apply_hoist(source, hoist));
    }
    current
}

fn eligible_call<'a>(
    operation: &'a Operation,
    env: ModuleEnv<'_>,
    will_return: &impl Fn(FunctionId) -> bool,
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
    if !will_return(*callee) {
        return None;
    }
    Some(call)
}

fn find_hoist(
    func: &Function,
    env: ModuleEnv<'_>,
    will_return: &impl Fn(FunctionId) -> bool,
) -> Option<Hoist> {
    let (successors, predecessors) = cfg(func);
    let dominance = Dominance::of(&successors, func.entry().as_index());
    let mut loops = natural_loops(func, &successors, &predecessors, &dominance);
    // Prefer the innermost loop. A later analysis may move the same call through an enclosing one.
    if loops.is_empty() {
        return None;
    }
    loops.sort_by_key(|natural| natural.blocks.len());

    let roots = PlaceRoots::of(func);
    let (definitions, allocas) = definitions(func);
    for natural in loops {
        // Canonical MIR's verifier currently requires definitions to precede uses in block-index
        // order as well as dominate them. The moved allocation can still be used in any loop block,
        // so require the preheader to precede the whole loop rather than only the call block.
        if natural
            .blocks
            .iter()
            .any(|block| natural.preheader.as_index() >= block.as_index())
        {
            continue;
        }
        let writes = writes_in(func, &natural.blocks, &roots);
        let preheader_writes = writes_in(func, &FxHashSet::from_iter([natural.preheader]), &roots);
        for block in func.blocks().filter(|block| natural.blocks.contains(block)) {
            for (index, operation) in func.block(block).operations().iter().enumerate() {
                let call_site = OperationSite {
                    block,
                    index: OperationIndex::from_index(index),
                };
                let Some(call) = eligible_call(operation, env, will_return) else {
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
                    || root_used_outside(func, output_root, &natural.blocks, &roots)
                {
                    continue;
                }

                let mut inputs = call
                    .extras
                    .iter()
                    .chain(call.arguments.iter().map(|(argument, _)| *argument))
                    .collect::<Vec<_>>();
                if inputs.iter().any(|input| {
                    roots
                        .root_of(input)
                        .is_none_or(|root| writes.contains_key(&root) || root == output_root)
                }) {
                    continue;
                }

                let move_alloca = natural.blocks.contains(&alloca.site.block);
                if move_alloca && !definition_dominates(alloca.site, call_site, &dominance) {
                    continue;
                }
                if !move_alloca {
                    inputs.push(call.result);
                }
                let Some(insertion) = insertion_point(
                    func,
                    &natural,
                    &definitions,
                    &dominance,
                    &inputs,
                    &roots,
                    &preheader_writes,
                ) else {
                    continue;
                };
                return Some(Hoist {
                    call: call_site,
                    alloca: move_alloca.then_some(alloca.site),
                    preheader: natural.preheader,
                    insertion,
                });
            }
        }
    }
    None
}

fn cfg(func: &Function) -> (Vec<Vec<usize>>, Vec<Vec<BlockId>>) {
    let count = func.blocks().count();
    let mut successors = vec![Vec::new(); count];
    let mut predecessors = vec![Vec::new(); count];
    for block in func.blocks() {
        for successor in func.block(block).terminator().successors() {
            successors[block.as_index()].push(successor.as_index());
            if !predecessors[successor.as_index()].contains(&block) {
                predecessors[successor.as_index()].push(block);
            }
        }
    }
    (successors, predecessors)
}

fn natural_loops(
    func: &Function,
    successors: &[Vec<usize>],
    predecessors: &[Vec<BlockId>],
    dominance: &Dominance,
) -> Vec<NaturalLoop> {
    let mut by_header = FxHashMap::<BlockId, FxHashSet<BlockId>>::default();
    for tail in func.blocks() {
        if !dominance.is_reachable(tail.as_index()) {
            continue;
        }
        for &header in &successors[tail.as_index()] {
            if !dominance.dominates(header, tail.as_index()) {
                continue;
            }
            let header = BlockId::from_index(header);
            let natural = by_header.entry(header).or_default();
            natural.insert(header);
            if natural.insert(tail) {
                let mut pending = vec![tail];
                while let Some(block) = pending.pop() {
                    for &predecessor in &predecessors[block.as_index()] {
                        if natural.insert(predecessor) && predecessor != header {
                            pending.push(predecessor);
                        }
                    }
                }
            }
        }
    }

    by_header
        .into_iter()
        .filter_map(|(header, blocks)| {
            let outside = predecessors[header.as_index()]
                .iter()
                .copied()
                .filter(|predecessor| !blocks.contains(predecessor))
                .collect::<Vec<_>>();
            let [preheader] = outside.as_slice() else {
                return None;
            };
            matches!(
                func.block(*preheader).terminator().kind,
                TerminatorKind::Goto { target } if target == header
            )
            .then_some(NaturalLoop {
                blocks,
                preheader: *preheader,
            })
        })
        .collect()
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
        OperationKind::Move => {
            write(&operation.operands[0]);
            write(&operation.operands[1]);
        }
        OperationKind::Clear | OperationKind::Drop { .. } | OperationKind::DropClosureEnv => {
            write(&operation.operands[0])
        }
        OperationKind::BuildArray { .. } => {
            if let Some(destination) = operation.operands.last() {
                write(destination);
            }
        }
        // These operations may consume captures or run scoped mutation. Treat every rooted operand
        // as changed rather than teaching LICM another operation's ownership contract.
        OperationKind::Project { .. }
        | OperationKind::EndProject
        | OperationKind::BuildSubscript { .. }
        | OperationKind::BuildClosure { .. } => operation.operands.iter().for_each(write),
        OperationKind::Alloca { .. }
        | OperationKind::AllocaPlace { .. }
        | OperationKind::CompareEqual
        | OperationKind::Load
        | OperationKind::Subfield { .. }
        | OperationKind::DictEntry { .. }
        | OperationKind::SubscriptMember { .. }
        | OperationKind::Variant { .. }
        | OperationKind::ExtractTag
        | OperationKind::StackSave
        | OperationKind::StackRestore
        | OperationKind::CheckCallDepth
        | OperationKind::CheckFuel
        | OperationKind::CloneClosureEnv { .. } => {}
    }
}

fn root_used_outside(
    func: &Function,
    root: Root,
    blocks: &FxHashSet<BlockId>,
    roots: &PlaceRoots,
) -> bool {
    for block in func.blocks().filter(|block| !blocks.contains(block)) {
        let basic = func.block(block);
        if basic
            .operations()
            .iter()
            .flat_map(|operation| operation.operands.iter())
            .chain(basic.terminator().operands())
            .any(|operand| roots.root_of(operand) == Some(root))
        {
            return true;
        }
    }
    false
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
    func: &Function,
    natural: &NaturalLoop,
    definitions: &FxHashMap<ValueId, OperationSite>,
    dominance: &Dominance,
    inputs: &[&mir::Value],
    roots: &PlaceRoots,
    preheader_writes: &FxHashMap<Root, Vec<OperationSite>>,
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

    let mut latest = func.block(natural.preheader).operations().len();
    for &block in &natural.blocks {
        for operation in func.block(block).operations() {
            if !matches!(operation.kind, OperationKind::StackRestore) {
                continue;
            }
            let mir::Value::Register(marker) = operation.operands[0] else {
                return None;
            };
            let definition = *definitions.get(&marker)?;
            if natural.blocks.contains(&definition.block) {
                continue;
            }
            if definition.block != natural.preheader {
                return None;
            }
            latest = latest.min(definition.index.as_index());
        }
    }
    // Insert as late as possible. Besides shortening the allocation's lifetime, this retains every
    // preheader computation and possible source failure before the speculative call while still
    // placing its storage ahead of a marker restored on the loop backedge.
    (earliest <= latest).then(|| OperationIndex::from_index(latest))
}

fn apply_hoist(func: &Function, hoist: Hoist) -> Function {
    let mut edit = FunctionEdit::new(func.clone());
    let call = edit
        .block_mut(hoist.call.block)
        .operations
        .remove(hoist.call.index.as_index());
    let alloca = hoist.alloca.map(|site| {
        let index = site.index.as_index()
            - usize::from(
                site.block == hoist.call.block
                    && site.index.as_index() > hoist.call.index.as_index(),
            );
        edit.block_mut(site.block).operations.remove(index)
    });

    let insertion = hoist.insertion.as_index();
    let operations = &mut edit.block_mut(hoist.preheader).operations;
    if let Some(alloca) = alloca {
        operations.insert(insertion, alloca);
        operations.insert(insertion + 1, call);
    } else {
        operations.insert(insertion, call);
    }
    edit.finish_unverified()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        CompilerSession, Location, MirOptimization,
        mir::{Operation, builder::FunctionBuilder, terminator::Terminator},
    };

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
        let alloca = body
            .find(&format!("{result} = alloca"))
            .unwrap_or_else(|| panic!("call result {result} has no allocation:\n{body}"));
        (call, alloca)
    }

    #[test]
    fn hoists_an_invariant_pure_call_before_the_loop_stack_marker() {
        let module = optimized(
            "fn invariant(x: int, y: int, n: int) {\n\
                 let mut total = 0;\n\
                 for i in 0..n { total = total + x * y };\n\
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
        // Larger than the inliner's per-callee operation budget, so the direct script call reaches
        // LICM. Its raw MIR is nevertheless an acyclic call DAG and proves `will_return`.
        let module = optimized(
            "fn large_sum(x: int) -> int {\n\
                 x + x + x + x + x + x + x + x + x + x +\n\
                 x + x + x + x + x + x + x + x + x + x\n\
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
        let marker = body.find("stack_save").expect("the loop has a marker");
        assert!(
            call < marker,
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
            preheader,
        };
        assert!(
            insertion_point(
                &function,
                &natural,
                &definitions,
                &dominance,
                &[],
                &PlaceRoots::of(&function),
                &FxHashMap::default(),
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
        let marker = body.find("stack_save").expect("the loop has a marker");
        assert!(
            marker < call,
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
        let marker = body
            .find("stack_save")
            .expect("the loop has a stack marker");
        assert!(
            multiply < marker,
            "LICM must be generic over concrete TrivialCopy result types:\n{body}"
        );
    }

    #[test]
    fn hoisted_storage_survives_iteration_restores_and_zero_trip_execution() {
        let source = "fn invariant(x: int, y: int, n: int) {\n\
                          let mut total = 0;\n\
                          for i in 0..n { total = total + x * y };\n\
                          total\n\
                      }\n\
                      fn main() { invariant(6, 7, 4) + invariant(6, 7, 0) }";
        let module = optimized(source);
        let body = body_of(&module, "invariant");
        let (_, result_alloca) = call_and_result_alloca(body, "call std::Num<std::int>::mul");
        let marker = body.find("stack_save").expect("the loop has a marker");
        assert!(
            result_alloca < marker,
            "this execution test must exercise the loop-local alloca moved with its call:\n{body}"
        );

        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        assert_eq!(session.eval_mir("licm_run", source), "168");
    }
}
