// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Method dependencies through the enclosing impl's evidence. Defaults are compiled
//! once, but recursion depends on the overrides selected by each implementation.

use super::emit_hir::PendingModuleFunctions;
use crate::{
    FxHashSet,
    desugar::DepGraphNode,
    graph::find_strongly_connected_components,
    hir::{self, NodeArena, NodeId, NodeKind, dictionary::DictionaryReq, hir_syn},
    module::{LocalFunctionId, PendingModuleFunction, TraitId, id::Id},
    types::{effects::EffType, r#trait::TraitMethodIndex, r#type::Type},
};

#[allow(clippy::too_many_arguments)]
pub(super) fn collect_method_calls(
    arena: &NodeArena,
    root: NodeId,
    trait_id: TraitId,
    input_tys: &[Type],
    method_count: usize,
    include_external_callbacks: bool,
    calls: &mut FxHashSet<TraitMethodIndex>,
) {
    // Defaults can close cycles through parent evidence or arbitrary helpers.
    // For default-bearing traits, conservatively model unknown callees as edges
    // to every slot. This extends the default/override graph without changing
    // the pre-existing recursion policy of impls with no default methods.
    // A unified evidence-aware call graph is needed to remove that distinction
    // without blocking inlining throughout the existing standard library.
    let has_trait_evidence = |requirements: &[DictionaryReq]| {
        requirements.iter().any(|requirement| {
            matches!(
                requirement,
                DictionaryReq::TraitImpl { trait_id: id, input_tys: inputs, .. }
                    if include_external_callbacks || (*id == trait_id && inputs == input_tys)
            )
        })
    };
    match &arena[root].kind {
        NodeKind::TraitMethodApply(call)
            if call.trait_id == trait_id && call.input_tys == input_tys =>
        {
            calls.insert(call.method_index);
        }
        NodeKind::GetTraitMethod(method)
            if method.trait_id == trait_id && method.input_tys == input_tys =>
        {
            calls.insert(method.method_index);
        }
        NodeKind::TraitMethodApply(_) | NodeKind::GetTraitMethod(_)
            if include_external_callbacks =>
        {
            calls.extend((0..method_count).map(TraitMethodIndex::from_index));
        }
        // A helper receiving trait evidence may participate in a cross-trait cycle.
        NodeKind::StaticApply(call)
            if include_external_callbacks || has_trait_evidence(&call.inst_data.dicts_req) =>
        {
            calls.extend((0..method_count).map(TraitMethodIndex::from_index));
        }
        NodeKind::GetFunction(function)
            if include_external_callbacks || has_trait_evidence(&function.inst_data.dicts_req) =>
        {
            calls.extend((0..method_count).map(TraitMethodIndex::from_index));
        }
        NodeKind::GetSubscript(subscript)
            if include_external_callbacks || has_trait_evidence(&subscript.inst_data.dicts_req) =>
        {
            calls.extend((0..method_count).map(TraitMethodIndex::from_index));
        }
        NodeKind::FunctionApply(_) | NodeKind::SubscriptApply(_) if include_external_callbacks => {
            calls.extend((0..method_count).map(TraitMethodIndex::from_index));
        }
        NodeKind::GetTraitAssociatedConst(constant)
            if constant.trait_id == trait_id && constant.input_tys == input_tys => {}
        _ => {}
    }
    for child in arena[root].kind.child_node_ids() {
        collect_method_calls(
            arena,
            child,
            trait_id,
            input_tys,
            method_count,
            include_external_callbacks,
            calls,
        );
    }
}

pub(super) fn guard_recursive_methods(
    calls: &[Vec<TraitMethodIndex>],
    functions: &[LocalFunctionId],
    pending: &mut PendingModuleFunctions,
) {
    let graph = calls
        .iter()
        .map(|calls| DepGraphNode(calls.iter().map(|index| index.as_index()).collect()))
        .collect::<Vec<_>>();
    for component in find_strongly_connected_components(&graph) {
        if component.len() == 1 && !graph[component[0]].0.contains(&component[0]) {
            continue;
        }
        for index in component {
            add_call_depth_guard(
                pending
                    .get_mut(&functions[index])
                    .expect("pending impl method"),
            );
        }
    }
}

fn add_call_depth_guard(function: &mut PendingModuleFunction) {
    let arena = &mut function.code.arena;
    let root = function.code.entry_node_id;
    let ty = arena[root].ty;
    let effects = arena[root].effects.clone();
    let span = arena[root].span;
    let check = arena.alloc(hir::Node::new(
        NodeKind::CheckCallDepth,
        Type::unit(),
        EffType::empty(),
        span,
    ));
    function.code.entry_node_id = arena.alloc(hir::Node::new(
        hir_syn::block(vec![check, root]),
        ty,
        effects,
        span,
    ));
}
