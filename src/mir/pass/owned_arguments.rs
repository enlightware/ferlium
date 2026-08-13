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

use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};
use ustr::ustr;

use crate::{
    compiler::Specialization,
    containers::{DenseBitSet, b},
    hir::function::ArgConvention,
    mir::{
        self, BlockId, Function, Operation, OperationKind, ParameterKind, edit::FunctionEdit,
        terminator::TerminatorKind,
    },
    module::{FunctionId, LocalFunctionId, ModuleEnv, ModuleId, id::Id, unique_generated_name},
    std::value::type_has_static_layout,
};

use super::{budget, dce, site::OperationIndex, stack_region};

#[derive(Clone)]
struct SourceBody {
    body: Function,
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
    sources: &'a [Option<SourceBody>],
    specializations: &'a mut Vec<Specialization>,
    env: ModuleEnv<'a>,
    cache: FxHashMap<VariantKey, Option<LocalFunctionId>>,
    active: FxHashSet<VariantKey>,
    generated: usize,
}

/// Rewrites last-use direct calls and appends the owned-ABI variants they require.
///
/// `functions` and the initial prefix of `specializations` are already fully optimized. Variants
/// are derived from that stable snapshot; appending one cannot change a later admission decision.
pub(crate) fn forward_owned_arguments(
    functions: &mut [Option<Function>],
    specializations: &mut Vec<Specialization>,
    module: ModuleId,
    env: ModuleEnv<'_>,
) {
    let first_index = functions.len();
    let initial_specializations = specializations.len();
    let mut sources = functions
        .iter()
        .enumerate()
        .map(|(index, body)| {
            body.as_ref().map(|body| SourceBody {
                body: body.clone(),
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
            body: specialization.body.clone(),
            original: specialization.original,
            is_specialization: true,
        })
    }));

    let mut rewritten = Vec::with_capacity(sources.len());
    {
        let mut factory = VariantFactory {
            module,
            first_index,
            sources: &sources,
            specializations,
            env,
            cache: FxHashMap::default(),
            active: FxHashSet::default(),
            generated: 0,
        };
        for source in &sources {
            rewritten.push(source.as_ref().map(|source| {
                rewrite_caller(&source.body, &mut factory).unwrap_or_else(|| source.body.clone())
            }));
        }
    }

    for (slot, body) in functions.iter_mut().zip(rewritten.drain(..first_index)) {
        *slot = body;
    }
    for (specialization, body) in specializations[..initial_specializations]
        .iter_mut()
        .zip(rewritten)
    {
        specialization.body = body.expect("a specialization always has a MIR body");
    }

    // Removing a clone strands its dispatch place/evidence; removing the caller's drop can do the
    // same. Cleanup every body once so variants and their callers finish in the same canonical form.
    for body in functions.iter_mut().flatten() {
        *body = cleanup(body.clone());
    }
    for specialization in specializations {
        specialization.body = cleanup(specialization.body.clone());
    }

    fn cleanup(mut body: Function) -> Function {
        if let Some(cleaned) = dce::remove_dead_storage(&body) {
            body = cleaned;
        }
        if let Some(cleaned) = stack_region::remove_redundant_stack_markers(&body) {
            body = cleaned;
        }
        body
    }
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
        if self.generated >= budget::MAX_OWNED_ARGUMENT_VARIANTS || !self.active.insert(key.clone())
        {
            return None;
        }

        let source = self
            .sources
            .get(callee.function.as_index())
            .and_then(Option::as_ref)
            .cloned();
        let rewritten = source.and_then(|source| {
            // An ordinary generic body can still read its dictionaries. Specializations have had
            // them bound already; ordinary dictionary-free functions and generated thunks are safe.
            if !source.is_specialization
                && source
                    .body
                    .parameters()
                    .iter()
                    .any(|parameter| matches!(parameter.kind, ParameterKind::Dictionary))
            {
                return None;
            }
            self.rewrite_variant(&source.body, &key.arguments)
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
            self.specializations
                .iter()
                .any(|specialization| specialization.name == candidate)
        });
        let mut edit = FunctionEdit::new(body);
        edit.set_name(name);
        body = edit.finish_unverified();

        let id = LocalFunctionId::from_index(self.first_index + self.specializations.len());
        self.specializations.push(Specialization {
            original,
            name,
            body,
        });
        self.generated += 1;
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
                ParameterKind::Parameter(convention) => Some((
                    mir::ParameterId::from_index(index),
                    convention,
                    parameter.ty,
                )),
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
            let metadata = metadata.get_or_insert_with(|| b(mir::CallMetadata::default()));
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
        let metadata = metadata.get_or_insert_with(|| b(mir::CallMetadata::default()));
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
    root: mir::ValueId,
    origins: &FxHashMap<mir::ValueId, mir::ValueId>,
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
    root: mir::ValueId,
    origins: &FxHashMap<mir::ValueId, mir::ValueId>,
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

fn place_origins(function: &Function) -> FxHashMap<mir::ValueId, mir::ValueId> {
    let mut origins = FxHashMap::default();
    for block in function.blocks() {
        for operation in function.block(block).operations() {
            let Some(result) = operation.result_id() else {
                continue;
            };
            match &operation.kind {
                OperationKind::Alloca { .. } => {
                    origins.insert(result, result);
                }
                OperationKind::Subfield { .. } => {
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

fn operand_root(
    operand: &mir::Value,
    origins: &FxHashMap<mir::ValueId, mir::ValueId>,
) -> Option<mir::ValueId> {
    let mir::Value::Register(value) = operand else {
        return None;
    };
    origins.get(value).copied()
}

fn predecessor_counts(function: &Function) -> Vec<usize> {
    let mut predecessors = vec![0; function.blocks().count()];
    for block in function.blocks() {
        let successors: Box<dyn Iterator<Item = BlockId>> =
            match &function.block(block).terminator().kind {
                TerminatorKind::Goto { target } => Box::new(std::iter::once(*target)),
                TerminatorKind::CondBr {
                    then_target,
                    else_target,
                    ..
                } => Box::new([*then_target, *else_target].into_iter()),
                TerminatorKind::Invoke { normal, error, .. } => {
                    Box::new([*normal, *error].into_iter())
                }
                TerminatorKind::Yield { resume, .. } => Box::new(std::iter::once(*resume)),
                TerminatorKind::Return
                | TerminatorKind::PropagateError
                | TerminatorKind::FailureDuringCleanup => Box::new(std::iter::empty()),
            };
        for successor in successors {
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
            TerminatorKind::Invoke { normal, error, .. } => {
                pending.push(*normal);
                pending.push(*error);
            }
            TerminatorKind::Yield { resume, .. } => pending.push(*resume),
            TerminatorKind::FailureDuringCleanup => {}
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
    use crate::{
        CompilerSession, Location, MirOptimization,
        mir::{BasicBlock, Function, Operation, terminator::Terminator},
    };

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
    fn map_pipeline_moves_last_use_array_and_mapper_through_the_thunk() {
        // A fully constant array pipeline now folds to `build_array` before this pass. Make the
        // array depend on a parameter while still creating an owned local copy, so this test keeps
        // exercising transfer of both the array and mapper rather than resource reification.
        let module =
            optimized("fn apply(xs: [int]) -> [int] { let mut ys = xs; ys |> map(|x| x*x) }");
        let entry = body_of(&module, "apply");
        assert!(
            entry.contains("#owned:[0,1](move %r0, move %r1, %p1)"),
            "the entry must transfer both dead arguments:\n{entry}"
        );
        let normal = entry
            .split("#owned:[0,1](move %r0, move %r1, %p1)")
            .nth(1)
            .expect("the owned call was asserted above")
            .split("\nfn ")
            .next()
            .unwrap();
        assert!(
            !normal.contains("drop (int) -> int %r1") && !normal.contains("drop [int] %r0"),
            "the transferred arguments must not retain drops after the call:\n{entry}"
        );

        let owned_map = module
            .split("fn Map<[A], B>::map#impl:")
            .skip(1)
            .find(|body| {
                body.lines()
                    .next()
                    .is_some_and(|header| header.contains("#owned:[0,1]("))
            })
            .unwrap_or_else(|| panic!("module has no owned map specialization:\n{module}"));
        let owned_map = owned_map.split("\nfn ").next().unwrap();
        assert!(
            owned_map.contains("@arg owned [int]")
                && owned_map.contains("@arg owned (int) -> int")
                && owned_map.contains("move %p0 to")
                && owned_map.contains("move %p1 to"),
            "the owned specialization must move both parameters into the iterator:\n{owned_map}"
        );
        assert!(
            !owned_map.contains("clone [int]") && !owned_map.contains("clone (int) -> int"),
            "the owned specialization must contain neither original clone:\n{owned_map}"
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
        let entry = crate::mir::BlockId::new(0);
        let normal = crate::mir::BlockId::new(1);
        let error = crate::mir::BlockId::new(2);
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

        assert!(!super::site_dominates_exits(
            &function,
            super::Site::Operation {
                block: normal,
                index: super::OperationIndex::new(0),
            }
        ));
        assert!(super::site_dominates_exits(
            &function,
            super::Site::Terminator { block: entry }
        ));
    }
}
