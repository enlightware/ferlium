// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

//! Forwarding a caller's last ownership into a callee.
//!
//! Source-level `let` parameters borrow: a callee that retains an argument clones it, and the
//! caller later drops its own value. Once MIR proves that drop is the caller's last use, the
//! `Value` laws make the pair equivalent to a move. The rewrite crosses a call boundary, so it
//! creates a cached optimized-MIR ABI variant whose selected parameters are [`ParameterKind::Owned`].
//! A variant either replaces the parameter's sole `clone` with `move`, or forwards ownership to
//! another such variant. This is deliberately after ordinary optimization and specialization: the
//! concrete clone and the forwarding thunk are visible then, and no earlier pass needs to reason
//! about the narrowed ABI.

use std::iter::once;

use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};
use ustr::ustr;

use super::{budget, dce, site::OperationIndex, stack_region};
use crate::{
    compiler::Specialization,
    containers::{DenseBitSet, b},
    hir::function::ArgConvention,
    mir::{
        self, BlockId, CallMetadata, Function, Operation, OperationKind, ParameterId,
        ParameterKind, ValueId, edit::FunctionEdit, terminator::TerminatorKind,
    },
    module::{FunctionId, LocalFunctionId, ModuleEnv, ModuleId, id::Id, unique_generated_name},
    std::value::type_has_static_layout,
};

#[derive(Clone, Copy)]
struct SourceBody<'a> {
    body: &'a Function,
    original: FunctionId,
    is_specialization: bool,
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct VariantKey {
    callee: FunctionId,
    arguments: DenseBitSet,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Site {
    Operation {
        block: BlockId,
        index: OperationIndex,
    },
    Terminator {
        block: BlockId,
    },
}

struct VariantFactory<'a> {
    module: ModuleId,
    first_index: usize,
    sources: &'a [Option<SourceBody<'a>>],
    existing_specializations: &'a [Specialization],
    generated_specializations: Vec<Specialization>,
    /// Fixed from `sources` before generation starts, so output cannot fund more output.
    limit: usize,
    env: ModuleEnv<'a>,
    cache: FxHashMap<VariantKey, Option<LocalFunctionId>>,
    active: FxHashSet<VariantKey>,
}

/// Rewrites last-use direct calls and appends the owned-ABI variants they require.
///
/// `functions` and the initial prefix of `specializations` are already fully optimized. Variants
/// are derived from that stable snapshot; generated bodies are accumulated separately, so one
/// cannot change a later admission decision.
pub(crate) fn forward_owned_arguments(
    functions: &mut [Option<Function>],
    specializations: &mut Vec<Specialization>,
    module: ModuleId,
    env: ModuleEnv<'_>,
) {
    // Inlining a forwarding thunk can expose the clone directly beside the aggregate that an
    // already-owned call consumes. Preserve the same ownership win even though there is no longer
    // a call boundary at the clone itself.
    for body in functions.iter_mut().flatten() {
        if let Some(rewritten) = forward_clones_into_owned_invokes(body) {
            *body = rewritten;
        }
    }
    for specialization in specializations.iter_mut() {
        if let Some(rewritten) = forward_clones_into_owned_invokes(&specialization.body) {
            specialization.body = rewritten;
        }
    }

    let first_index = functions.len();
    let initial_specializations = specializations.len();
    // Keep the source population stable while variants recursively request other variants. New
    // bodies accumulate separately, so the table can borrow the existing bodies instead of deeply
    // cloning every one before finding out whether any caller changes.
    let (mut rewritten, generated_specializations) = {
        let mut sources = functions
            .iter()
            .enumerate()
            .map(|(index, body)| {
                body.as_ref().map(|body| SourceBody {
                    body,
                    original: FunctionId {
                        module,
                        function: LocalFunctionId::from_index(index),
                    },
                    is_specialization: false,
                })
            })
            .collect::<Vec<_>>();
        sources.extend(specializations.iter().map(|specialization| {
            Some(SourceBody {
                body: &specialization.body,
                original: specialization.original,
                is_specialization: true,
            })
        }));
        let limit = budget::owned_argument_variant_limit(sources.iter().flatten().count());

        let mut factory = VariantFactory {
            module,
            first_index,
            sources: &sources,
            existing_specializations: specializations,
            generated_specializations: Vec::new(),
            limit,
            env,
            cache: FxHashMap::default(),
            active: FxHashSet::default(),
        };
        let rewritten = sources
            .iter()
            .map(|source| {
                source
                    .as_ref()
                    .and_then(|source| rewrite_caller(source.body, &mut factory))
            })
            .collect::<Vec<_>>();
        (rewritten, factory.generated_specializations)
    };

    for (slot, body) in functions.iter_mut().zip(rewritten.drain(..first_index)) {
        if let Some(body) = body {
            *slot = Some(body);
        }
    }
    for (specialization, body) in specializations[..initial_specializations]
        .iter_mut()
        .zip(rewritten)
    {
        if let Some(body) = body {
            specialization.body = body;
        }
    }
    specializations.extend(generated_specializations);

    // Caller rewriting above may itself have made the consuming invoke owned, so expose local
    // clone-to-move forwarding once more on the settled call graph.
    for body in functions.iter_mut().flatten() {
        if let Some(rewritten) = forward_clones_into_owned_invokes(body) {
            *body = rewritten;
        }
    }
    for specialization in specializations.iter_mut() {
        if let Some(rewritten) = forward_clones_into_owned_invokes(&specialization.body) {
            specialization.body = rewritten;
        }
    }

    // Removing a clone strands its dispatch place/evidence; removing the caller's drop can do the
    // same. Cleanup every body once so variants and their callers finish in the same canonical form.
    for body in functions.iter_mut().flatten() {
        if let Some(cleaned) = cleanup(body) {
            *body = cleaned;
        }
    }
    for specialization in specializations {
        if let Some(cleaned) = cleanup(&specialization.body) {
            specialization.body = cleaned;
        }
    }

    fn cleanup(body: &Function) -> Option<Function> {
        let mut current = dce::remove_dead_storage(body);
        let source = current.as_ref().unwrap_or(body);
        if let Some(cleaned) = stack_region::remove_redundant_stack_markers(source) {
            current = Some(cleaned);
        }
        current
    }
}

/// Replace a clone with a move when its destination is part of an aggregate consumed by an owned
/// invoke and the source is otherwise only dropped on both successor paths.
///
/// This is the intraprocedural form of the ordinary caller/callee forwarding below. It appears
/// after inlining a small forwarding thunk: the callee's clone now initializes a subfield in the
/// caller, while the owned downstream call and the source's two cleanup drops remain explicit.
fn forward_clones_into_owned_invokes(source: &Function) -> Option<Function> {
    if !may_forward_clones_into_owned_invokes(source) {
        return None;
    }
    let origins = place_origins(source);
    let predecessors = predecessor_counts(source);
    let mut rewrites = Vec::new();
    let mut removed_drops = FxHashSet::default();

    for block in source.blocks() {
        let TerminatorKind::Invoke {
            operation: invoke, ..
        } = &source.block(block).terminator().kind
        else {
            continue;
        };
        let OperationKind::Call { ty, metadata } = &invoke.kind else {
            continue;
        };
        let Some(metadata) = metadata.as_deref() else {
            continue;
        };
        if metadata.owned_arguments.is_empty() {
            continue;
        }
        let visible_start = invoke.operands.len() - (ty.fn_ty.args.len() + 1);

        for (index, operation) in source.block(block).operations().iter().enumerate() {
            let OperationKind::Clone { .. } = operation.kind else {
                continue;
            };
            let [clone_source, destination, ..] = operation.operands.as_ref() else {
                continue;
            };
            let Some(source_root) = operand_root(clone_source, &origins) else {
                continue;
            };
            let Some(destination_root) = operand_root(destination, &origins) else {
                continue;
            };
            let destination_is_consumed = metadata.owned_arguments.iter_ones().any(|argument| {
                operand_root(&invoke.operands[visible_start + argument], &origins)
                    == Some(destination_root)
            });
            let later_use = operations_use_root(
                source.block(block).operations()[index + 1..]
                    .iter()
                    .chain(once(invoke)),
                source_root,
                &origins,
            );
            if !destination_is_consumed || later_use {
                continue;
            }
            let site = Site::Operation {
                block,
                index: OperationIndex::from_index(index),
            };
            if !site_dominates_exits(source, site) {
                continue;
            }
            let Some(drops) = terminal_drops(
                source,
                Site::Terminator { block },
                clone_source,
                source_root,
                &origins,
                &predecessors,
            ) else {
                continue;
            };
            if drops.iter().any(|drop| removed_drops.contains(drop)) {
                continue;
            }
            removed_drops.extend(drops.iter().copied());
            rewrites.push((site, clone_source.clone(), destination.clone(), drops));
        }
    }

    if rewrites.is_empty() {
        return None;
    }
    let mut edit = FunctionEdit::new(source.clone());
    let mut drops_by_block: FxHashMap<BlockId, Vec<OperationIndex>> = FxHashMap::default();
    for (site, source, destination, drops) in rewrites {
        let operation = operation_at_mut(&mut edit, site);
        operation.operands = Box::new([source, destination]);
        operation.kind = OperationKind::Move;
        for drop in drops {
            let Site::Operation { block, index } = drop else {
                unreachable!("drop is always a non-terminating operation")
            };
            drops_by_block.entry(block).or_default().push(index);
        }
    }
    for (block, indices) in drops_by_block {
        let operations = &mut edit.block_mut(block).operations;
        for index in indices
            .into_iter()
            .sorted_by_key(|index| index.as_index())
            .rev()
        {
            operations.remove(index.as_index());
        }
    }
    Some(edit.finish_unverified())
}

/// Cheaply rejects the overwhelmingly common bodies for which the data-flow preparation below
/// cannot produce a rewrite. The clone and owned invoke need not be in the same block: allowing
/// that false positive keeps this prefilter purely syntactic and therefore unable to hide a valid
/// forwarding opportunity.
fn may_forward_clones_into_owned_invokes(source: &Function) -> bool {
    let mut has_clone = false;
    let mut has_owned_invoke = false;
    for block in source.blocks() {
        let block = source.block(block);
        has_clone |= block
            .operations()
            .iter()
            .any(|operation| matches!(operation.kind, OperationKind::Clone { .. }));
        has_owned_invoke |= match &block.terminator().kind {
            TerminatorKind::Invoke { operation, .. } => match &operation.kind {
                OperationKind::Call { metadata, .. } => metadata
                    .as_deref()
                    .is_some_and(|metadata| !metadata.owned_arguments.is_empty()),
                _ => false,
            },
            _ => false,
        };
        if has_clone && has_owned_invoke {
            return true;
        }
    }
    false
}

fn operations_use_root<'a>(
    operations: impl Iterator<Item = &'a Operation>,
    root: ValueId,
    origins: &FxHashMap<ValueId, ValueId>,
) -> bool {
    operations
        .flat_map(|operation| operation.operands.iter())
        .any(|operand| operand_root(operand, origins) == Some(root))
}

impl VariantFactory<'_> {
    fn variant_for(&mut self, callee: FunctionId, arguments: DenseBitSet) -> Option<FunctionId> {
        if arguments.is_empty() || callee.module != self.module {
            return None;
        }
        let key = VariantKey { callee, arguments };
        if let Some(cached) = self.cache.get(&key) {
            return cached.map(|function| FunctionId {
                module: self.module,
                function,
            });
        }
        if self.generated_specializations.len() >= self.limit || !self.active.insert(key.clone()) {
            return None;
        }

        let source = self
            .sources
            .get(callee.function.as_index())
            .and_then(Option::as_ref)
            .copied();
        let rewritten = source.and_then(|source| {
            // An ordinary generic body can still read its dictionaries. Specializations have had
            // them bound already; ordinary dictionary-free functions and generated thunks are safe.
            // Thunks are type-monomorphic wrappers whose evidence parameters stay positional and
            // unchanged in an owned-ABI variant.
            if !source.is_specialization
                && !source.body.name.as_str().ends_with("-thunk")
                && source
                    .body
                    .parameters()
                    .iter()
                    .any(|parameter| matches!(parameter.kind, ParameterKind::Dictionary))
            {
                return None;
            }
            self.rewrite_variant(source.body, &key.arguments)
                .map(|body| (source.original, body))
        });
        self.active.remove(&key);

        let Some((original, mut body)) = rewritten else {
            self.cache.insert(key, None);
            return None;
        };
        let suffix = key.arguments.iter_ones().join(",");
        let base = ustr(&format!("{}#owned:[{suffix}]", body.name));
        let name = unique_generated_name(base, |candidate| {
            self.existing_specializations
                .iter()
                .chain(&self.generated_specializations)
                .any(|specialization| specialization.name == candidate)
        });
        let mut edit = FunctionEdit::new(body);
        edit.set_name(name);
        body = edit.finish_unverified();

        let id = LocalFunctionId::from_index(
            self.first_index
                + self.existing_specializations.len()
                + self.generated_specializations.len(),
        );
        self.generated_specializations.push(Specialization {
            original,
            name,
            body,
        });
        self.cache.insert(key, Some(id));
        Some(FunctionId {
            module: self.module,
            function: id,
        })
    }

    fn rewrite_variant(&mut self, source: &Function, arguments: &DenseBitSet) -> Option<Function> {
        let visible = source
            .parameters()
            .iter()
            .enumerate()
            .filter_map(|(index, parameter)| match parameter.kind {
                ParameterKind::Parameter(convention) => {
                    Some((ParameterId::from_index(index), convention, parameter.ty))
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        if arguments
            .iter_ones()
            .any(|index| !matches!(visible.get(index), Some((_, ArgConvention::Let, _))))
        {
            return None;
        }

        let mut clone_sites = FxHashSet::default();
        let mut forwarding: FxHashMap<Site, DenseBitSet> = FxHashMap::default();
        for argument in arguments.iter_ones() {
            let parameter = mir::Value::Parameter(visible[argument].0);
            let (site, operand_index) = sole_use(source, &parameter)?;
            // The owned ABI promises consumption on every returning path. A single syntactic use
            // is insufficient when an earlier source failure or branch can bypass it.
            if !site_dominates_exits(source, site) {
                return None;
            }
            let operation = operation_at(source, site);
            match &operation.kind {
                OperationKind::Clone { ty }
                    if operand_index == 0
                        && type_has_static_layout(*ty, operation.span, &self.env) =>
                {
                    clone_sites.insert(site);
                }
                OperationKind::Call { ty, metadata } => {
                    if metadata
                        .as_deref()
                        .is_some_and(|metadata| !metadata.owned_arguments.is_empty())
                    {
                        return None;
                    }
                    let visible_start = operation.operands.len() - (ty.fn_ty.args.len() + 1);
                    if operand_index < visible_start
                        || operand_index >= visible_start + ty.fn_ty.args.len()
                    {
                        return None;
                    }
                    let forwarded = operand_index - visible_start;
                    if ty.fn_ty.args[forwarded]
                        .mut_ty
                        .as_resolved()
                        .is_some_and(|mutability| mutability.is_mutable())
                    {
                        return None;
                    }
                    forwarding.entry(site).or_default().insert(forwarded);
                }
                _ => return None,
            }
        }

        let mut forwarded_variants = Vec::with_capacity(forwarding.len());
        for (site, mask) in forwarding {
            let operation = operation_at(source, site);
            let mir::Value::Function(callee) = operation.operands[0] else {
                return None;
            };
            let variant = self.variant_for(callee, mask.clone())?;
            forwarded_variants.push((site, variant, mask));
        }

        let mut edit = FunctionEdit::new(source.clone());
        let mut visible_index = 0;
        for parameter in edit.parameters_mut() {
            if matches!(parameter.kind, ParameterKind::Parameter(_)) {
                if arguments.contains(visible_index) {
                    parameter.kind = ParameterKind::Owned;
                }
                visible_index += 1;
            }
        }
        for site in clone_sites {
            let operation = operation_at_mut(&mut edit, site);
            let source = operation.operands[0].clone();
            let destination = operation.operands[1].clone();
            operation.operands = Box::new([source, destination]);
            operation.kind = OperationKind::Move;
        }
        for (site, variant, mask) in forwarded_variants {
            let operation = operation_at_mut(&mut edit, site);
            operation.operands[0] = mir::Value::Function(variant);
            let OperationKind::Call { metadata, .. } = &mut operation.kind else {
                unreachable!("a forwarding sink was classified as a call")
            };
            let metadata = metadata.get_or_insert_with(|| b(CallMetadata::default()));
            metadata.owned_arguments.union_with(&mask);
        }
        Some(edit.finish_unverified())
    }
}

#[derive(Clone)]
struct CallerRewrite {
    call: Site,
    callee: FunctionId,
    arguments: DenseBitSet,
    drops: Vec<Site>,
}

fn rewrite_caller(source: &Function, factory: &mut VariantFactory<'_>) -> Option<Function> {
    let origins = place_origins(source);
    let predecessors = predecessor_counts(source);
    let call_sites = all_operations(source)
        .filter_map(|(site, operation)| {
            matches!(operation.kind, OperationKind::Call { .. }).then_some(site)
        })
        .collect::<Vec<_>>();
    let mut rewrites = Vec::new();
    let mut removed_drops = FxHashSet::default();

    for call in call_sites {
        let operation = operation_at(source, call);
        let OperationKind::Call { ty, metadata } = &operation.kind else {
            unreachable!()
        };
        if metadata
            .as_deref()
            .is_some_and(|metadata| !metadata.owned_arguments.is_empty())
        {
            continue;
        }
        let mir::Value::Function(callee) = operation.operands[0] else {
            continue;
        };
        if callee.module != factory.module || callee.function.as_index() >= factory.sources.len() {
            continue;
        }
        let visible_start = operation.operands.len() - (ty.fn_ty.args.len() + 1);
        let mut candidates = Vec::new();
        for argument in 0..ty.fn_ty.args.len() {
            if ty.fn_ty.args[argument]
                .mut_ty
                .as_resolved()
                .is_some_and(|mutability| mutability.is_mutable())
            {
                continue;
            }
            let operand_index = visible_start + argument;
            let operand = &operation.operands[operand_index];
            let mir::Value::Register(root) = operand else {
                continue;
            };
            if origins.get(root) != Some(root)
                || operation.operands.iter().enumerate().any(|(index, other)| {
                    index != operand_index && operand_root(other, &origins) == Some(*root)
                })
            {
                continue;
            }
            let Some(drops) = terminal_drops(source, call, operand, *root, &origins, &predecessors)
            else {
                continue;
            };
            candidates.push((argument, drops));
        }
        if candidates.is_empty() {
            continue;
        }

        let mut mask = DenseBitSet::empty();
        for (argument, _) in &candidates {
            mask.insert(*argument);
        }
        let variant = match factory.variant_for(callee, mask.clone()) {
            Some(variant) => Some((variant, mask, candidates)),
            None => candidates
                .into_iter()
                .find_map(|candidate @ (argument, _)| {
                    let mut mask = DenseBitSet::empty();
                    mask.insert(argument);
                    factory
                        .variant_for(callee, mask.clone())
                        .map(|variant| (variant, mask, vec![candidate]))
                }),
        };
        let Some((callee, arguments, candidates)) = variant else {
            continue;
        };
        let drops = candidates
            .into_iter()
            .flat_map(|(_, drops)| drops)
            .collect::<Vec<_>>();
        if drops.iter().any(|drop| removed_drops.contains(drop)) {
            continue;
        }
        removed_drops.extend(drops.iter().copied());
        rewrites.push(CallerRewrite {
            call,
            callee,
            arguments,
            drops,
        });
    }

    if rewrites.is_empty() {
        return None;
    }
    let mut edit = FunctionEdit::new(source.clone());
    for rewrite in &rewrites {
        let operation = operation_at_mut(&mut edit, rewrite.call);
        operation.operands[0] = mir::Value::Function(rewrite.callee);
        let OperationKind::Call { metadata, .. } = &mut operation.kind else {
            unreachable!()
        };
        let metadata = metadata.get_or_insert_with(|| b(CallMetadata::default()));
        metadata.owned_arguments.union_with(&rewrite.arguments);
    }
    let mut drops_by_block: FxHashMap<BlockId, Vec<OperationIndex>> = FxHashMap::default();
    for rewrite in rewrites {
        for drop in rewrite.drops {
            let Site::Operation { block, index } = drop else {
                unreachable!("drop is always a non-terminating operation")
            };
            drops_by_block.entry(block).or_default().push(index);
        }
    }
    for (block, indices) in drops_by_block {
        let operations = &mut edit.block_mut(block).operations;
        for index in indices
            .into_iter()
            .sorted_by_key(|index| index.as_index())
            .rev()
        {
            operations.remove(index.as_index());
        }
    }
    Some(edit.finish_unverified())
}

fn terminal_drops(
    function: &Function,
    call: Site,
    operand: &mir::Value,
    root: ValueId,
    origins: &FxHashMap<ValueId, ValueId>,
    predecessors: &[usize],
) -> Option<Vec<Site>> {
    match call {
        Site::Operation { block, index } => {
            if !matches!(
                function.block(block).terminator().kind,
                TerminatorKind::Return
            ) {
                return None;
            }
            let drop = sole_drop_in_operations(
                function.block(block).operations(),
                index.as_index() + 1,
                operand,
                root,
                origins,
            )?;
            Some(vec![Site::Operation { block, index: drop }])
        }
        Site::Terminator { block } => {
            let TerminatorKind::Invoke { normal, error, .. } =
                function.block(block).terminator().kind
            else {
                return None;
            };
            let mut drops = Vec::with_capacity(2);
            for successor in [normal, error] {
                if predecessors[successor.as_index()] != 1
                    || !matches!(
                        function.block(successor).terminator().kind,
                        TerminatorKind::Return | TerminatorKind::PropagateError
                    )
                {
                    return None;
                }
                let index = sole_drop_in_operations(
                    function.block(successor).operations(),
                    0,
                    operand,
                    root,
                    origins,
                )?;
                drops.push(Site::Operation {
                    block: successor,
                    index,
                });
            }
            Some(drops)
        }
    }
}

fn sole_drop_in_operations(
    operations: &[Operation],
    start: usize,
    operand: &mir::Value,
    root: ValueId,
    origins: &FxHashMap<ValueId, ValueId>,
) -> Option<OperationIndex> {
    let mut found = None;
    for (index, operation) in operations.iter().enumerate().skip(start) {
        if matches!(operation.kind, OperationKind::Drop { .. }) && operation.operands[0] == *operand
        {
            if found.replace(OperationIndex::from_index(index)).is_some() {
                return None;
            }
            continue;
        }
        if operation
            .operands
            .iter()
            .any(|value| operand_root(value, origins) == Some(root))
        {
            return None;
        }
    }
    found
}

fn sole_use(function: &Function, value: &mir::Value) -> Option<(Site, usize)> {
    let mut found = None;
    for (site, operation) in all_operations(function) {
        for (index, operand) in operation.operands.iter().enumerate() {
            if operand == value {
                if found.replace((site, index)).is_some() {
                    return None;
                }
            }
        }
    }
    found
}

fn place_origins(function: &Function) -> FxHashMap<ValueId, ValueId> {
    let mut origins = FxHashMap::default();
    for block in function.blocks() {
        for operation in function.block(block).operations() {
            let Some(result) = operation.result_id() else {
                continue;
            };
            match &operation.kind {
                OperationKind::Alloca { .. } | OperationKind::RuntimeAlloc { .. } => {
                    origins.insert(result, result);
                }
                OperationKind::Subfield { .. }
                | OperationKind::AddressOffset { .. }
                | OperationKind::AddressOffsetPlace { .. } => {
                    if let Some(root) = operand_root(&operation.operands[0], &origins) {
                        origins.insert(result, root);
                    }
                }
                OperationKind::Project { ty, .. } => {
                    // A scoped accessor's exposed place is rooted in its receiver. Recording that
                    // origin makes its eventual `end_project` (or any other later use) prevent us
                    // from transferring the receiver while the projection is live.
                    let visible_start = operation.operands.len() - ty.fn_ty.args.len();
                    if let Some(root) = operand_root(&operation.operands[visible_start], &origins) {
                        origins.insert(result, root);
                    }
                }
                _ => {}
            }
        }
    }
    origins
}

fn operand_root(operand: &mir::Value, origins: &FxHashMap<ValueId, ValueId>) -> Option<ValueId> {
    let mir::Value::Register(value) = operand else {
        return None;
    };
    origins.get(value).copied()
}

fn predecessor_counts(function: &Function) -> Vec<usize> {
    let mut predecessors = vec![0; function.blocks().count()];
    for block in function.blocks() {
        for successor in function.block(block).terminator().successors() {
            predecessors[successor.as_index()] += 1;
        }
    }
    predecessors
}

/// Whether every ordinary or source-error exit reachable from entry passes through `site`.
///
/// Operations within a block are straight-line, and an invoked operation runs before either of
/// its successor edges, so reaching the site's block is enough to establish consumption. Paths
/// that never exit need no separate obligation; sandbox termination reclaims their frames.
fn site_dominates_exits(function: &Function, site: Site) -> bool {
    let sink = match site {
        Site::Operation { block, .. } | Site::Terminator { block } => block,
    };
    let mut pending = vec![function.entry()];
    let mut visited = DenseBitSet::empty();
    while let Some(block) = pending.pop() {
        if block == sink || visited.contains(block.as_index()) {
            continue;
        }
        visited.insert(block.as_index());
        match &function.block(block).terminator().kind {
            TerminatorKind::Return | TerminatorKind::PropagateError => return false,
            TerminatorKind::Goto { target } => pending.push(*target),
            TerminatorKind::CondBr {
                then_target,
                else_target,
                ..
            } => {
                pending.push(*then_target);
                pending.push(*else_target);
            }
            TerminatorKind::SwitchVariant { cases, default, .. } => {
                pending.extend(cases.iter().map(|(_, target)| *target));
                pending.push(*default);
            }
            TerminatorKind::Invoke { normal, error, .. } => {
                pending.push(*normal);
                pending.push(*error);
            }
            TerminatorKind::Yield { resume, .. } => pending.push(*resume),
            TerminatorKind::FailureDuringCleanup | TerminatorKind::InvariantFailure { .. } => {}
        }
    }
    true
}

fn all_operations(function: &Function) -> impl Iterator<Item = (Site, &Operation)> {
    function.blocks().flat_map(|block| {
        function
            .block(block)
            .operations()
            .iter()
            .enumerate()
            .map(move |(index, operation)| {
                (
                    Site::Operation {
                        block,
                        index: OperationIndex::from_index(index),
                    },
                    operation,
                )
            })
            .chain(match &function.block(block).terminator().kind {
                TerminatorKind::Invoke { operation, .. } => {
                    Some((Site::Terminator { block }, operation))
                }
                _ => None,
            })
    })
}

fn operation_at(function: &Function, site: Site) -> &Operation {
    match site {
        Site::Operation { block, index } => &function.block(block).operations()[index.as_index()],
        Site::Terminator { block } => match &function.block(block).terminator().kind {
            TerminatorKind::Invoke { operation, .. } => operation,
            _ => unreachable!("terminator site must name an invoke"),
        },
    }
}

fn operation_at_mut(edit: &mut FunctionEdit, site: Site) -> &mut Operation {
    match site {
        Site::Operation { block, index } => &mut edit.block_mut(block).operations[index.as_index()],
        Site::Terminator { block } => match &mut edit.block_mut(block).terminator.kind {
            TerminatorKind::Invoke { operation, .. } => operation,
            _ => unreachable!("terminator site must name an invoke"),
        },
    }
}

#[cfg(test)]
mod tests {
    use std::iter::once;

    use rustc_hash::FxHashMap;

    use super::{OperationIndex, Site, operations_use_root, site_dominates_exits};
    use crate::{
        CompilerSession, Location, MirOptimization,
        mir::{BasicBlock, BlockId, Function, Operation, Value, ValueId, terminator::Terminator},
    };

    #[test]
    fn an_invoke_operand_counts_as_a_later_use_for_clone_forwarding() {
        let span = Location::new_synthesized();
        let source_id = ValueId::new(0);
        let destination_id = ValueId::new(1);
        let source = Value::Register(source_id);
        let destination = Value::Register(destination_id);
        let invoke = Operation::move_value(span, source, destination);
        let origins =
            FxHashMap::from_iter([(source_id, source_id), (destination_id, destination_id)]);

        assert!(operations_use_root(once(&invoke), source_id, &origins,));
    }

    fn optimized(source: &str) -> String {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        session.emit_mir("owned_arguments", source)
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

    #[test]
    fn map_pipeline_moves_last_use_array_and_mapper_after_thunk_inlining() {
        // A fully constant array pipeline now folds to `build_array` before this pass. Make the
        // array depend on a parameter while still creating an owned local copy, so this test keeps
        // exercising transfer of both the array and mapper rather than resource reification.
        let module =
            optimized("fn apply(xs: [int]) -> [int] { let mut ys = xs; ys |> map(|x| x*x) }");
        let entry = body_of(&module, "apply");
        assert!(
            entry.contains("#owned:[0,1]")
                && entry.contains("move %r0")
                && entry.contains("move %r1"),
            "the owned thunk call must consume both dead arguments:\n{entry}"
        );
        assert!(
            !entry.contains("drop (int) -> int %r1") && !entry.contains("drop [int] %r0"),
            "the transferred arguments must not retain drops after the call:\n{entry}"
        );
    }

    #[test]
    fn a_still_live_caller_value_keeps_the_borrowing_call_and_clone() {
        let module = optimized(
            "fn snapshot(value: [int]) -> [int] { let mut result = value; result }\n\
             let source = [1, 2];\n\
             let copied = snapshot(source);\n\
             concat(source, copied)",
        );
        assert!(
            !module.contains("snapshot#owned:"),
            "a source used after the call must not transfer ownership:\n{module}"
        );
        let snapshot = body_of(&module, "snapshot");
        assert!(
            snapshot.contains("clone [int] %p0"),
            "the borrowing implementation must retain its semantic clone:\n{snapshot}"
        );
    }

    #[test]
    fn optimized_owned_map_pipeline_executes() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        assert_eq!(
            session.eval_mir(
                "owned_arguments_run",
                "fn main() -> [int] { [1, 2] |> concat([3, 4]) |> map(|x| x*x) }",
            ),
            "[1, 4, 9, 16]"
        );
    }

    #[test]
    fn an_earlier_error_exit_prevents_an_owned_variant() {
        let span = Location::new_synthesized();
        let entry = BlockId::new(0);
        let normal = BlockId::new(1);
        let error = BlockId::new(2);
        let function = Function::new(
            "fallible_before_sink".into(),
            Default::default(),
            vec![],
            vec![],
            vec![
                BasicBlock::new(
                    vec![],
                    Terminator::invoke(span, Operation::check_fuel(span), normal, error),
                ),
                BasicBlock::new(vec![Operation::check_fuel(span)], Terminator::ret(span)),
                BasicBlock::new(vec![], Terminator::propagate_error(span)),
            ],
        );

        assert!(!site_dominates_exits(
            &function,
            Site::Operation {
                block: normal,
                index: OperationIndex::new(0),
            }
        ));
        assert!(site_dominates_exits(
            &function,
            Site::Terminator { block: entry }
        ));
    }
}
