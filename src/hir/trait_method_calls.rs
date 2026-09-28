// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Method dependencies through the enclosing impl's evidence. Defaults are compiled
//! once, but recursion depends on the overrides selected by each implementation.

use super::emit_hir::PendingModuleFunctions;
use crate::{
    FxHashMap, FxHashSet,
    desugar::DepGraphNode,
    graph::find_strongly_connected_components,
    hir::{self, NodeArena, NodeId, NodeKind, dictionary::DictionaryReq, hir_syn},
    module::{
        FunctionId, LocalFunctionId, ModuleEnv, PendingModuleFunction, ResolvedLocalClone,
        ResolvedTakeLocalValueMode, TraitId, id::Id,
    },
    types::{effects::EffType, r#trait::TraitMethodIndex, r#type::Type},
};

/// A local proof that a completed helper cannot call back into script through an
/// unknown target. Pending bodies, cycles and unmodelled operations stay unknown.
/// In particular, ownership operations can hide calls to user-defined Value methods.
#[derive(Default)]
pub(super) struct CallbackFreeFunctions {
    proven: FxHashMap<FunctionId, bool>,
}

impl CallbackFreeFunctions {
    fn contains(&mut self, id: FunctionId, env: ModuleEnv<'_>) -> bool {
        if let Some(&answer) = self.proven.get(&id) {
            return answer;
        }
        self.proven.insert(id, false);
        let Some(module) = env.module_by_id(id.module) else {
            return false;
        };
        let Some(function) = module.get_function_by_id(id.function) else {
            return false;
        };
        // Only native entries carry the no-reentry contract. Interpreter-only host
        // callbacks expose EvalCtx and are deliberately not covered by this proof.
        let answer = function.code.native_entry().is_some()
            || function.code.as_script().is_some_and(|script| {
                script.yield_node_id.is_none()
                    && self.node(&module.hir_arena, script.entry_node_id, env)
            });
        self.proven.insert(id, answer);
        answer
    }

    fn node(&mut self, arena: &hir::ENodeArena, id: hir::ENodeId, env: ModuleEnv<'_>) -> bool {
        use hir::NodeKind::*;
        match &arena[id].kind {
            Immediate(_) | LoadLocal(_) | CheckFuel => true,
            Tuple(values) | Record(values) | Array(values) => {
                values.iter().all(|id| self.node(arena, *id, env))
            }
            Variant(value) => self.node(arena, value.payload, env),
            Project(value) => self.node(arena, value.value, env),
            StoreLocal(value) => self.node(arena, value.value, env),
            Return(value) => self.node(arena, *value, env),
            CloneValue(value) if value.clone == ResolvedLocalClone::TrivialCopy => {
                self.node(arena, value.source, env)
            }
            TakeLocalValue(value) => matches!(
                value.mode,
                ResolvedTakeLocalValueMode::MoveOwned
                    | ResolvedTakeLocalValueMode::CloneBorrowed(ResolvedLocalClone::TrivialCopy)
            ),
            Block(block) => {
                block.cleanup.is_empty() && block.body.iter().all(|id| self.node(arena, *id, env))
            }
            Case(case) => {
                self.node(arena, case.value, env)
                    && case
                        .alternatives
                        .iter()
                        .all(|(_, id)| self.node(arena, *id, env))
                    && self.node(arena, case.default, env)
            }
            StaticApply(call) => {
                call.inst_data.dicts_req.is_empty()
                    && call.extra_arguments.is_empty()
                    && self.contains(call.function, env)
                    && call
                        .arguments
                        .iter()
                        .all(|arg| self.node(arena, arg.value, env))
            }
            _ => false,
        }
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn collect_method_calls(
    arena: &NodeArena,
    root: NodeId,
    trait_id: TraitId,
    input_tys: &[Type],
    method_count: usize,
    include_external_callbacks: bool,
    calls: &mut FxHashSet<TraitMethodIndex>,
    callback_free: &mut CallbackFreeFunctions,
    env: ModuleEnv<'_>,
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
            if has_trait_evidence(&call.inst_data.dicts_req)
                || (include_external_callbacks && !callback_free.contains(call.function, env)) =>
        {
            calls.extend((0..method_count).map(TraitMethodIndex::from_index));
        }
        NodeKind::GetFunction(function)
            if has_trait_evidence(&function.inst_data.dicts_req)
                || (include_external_callbacks
                    && !callback_free.contains(function.function, env)) =>
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
            callback_free,
            env,
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CompilerSession, MirOptimization};

    #[test]
    fn native_comparisons_and_their_script_helper_are_callback_free() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let module = env.module_by_id(crate::std::STD_MODULE_ID).unwrap();
        let mut proof = CallbackFreeFunctions::default();
        for name in [
            "lt_int",
            "le_float",
            "compare_string_code",
            "ordering_from_code",
        ] {
            let id = module.get_local_function_id(ustr::ustr(name)).unwrap();
            assert!(
                proof.contains(FunctionId::new(module.module_id(), id), env),
                "{name}"
            );
        }
    }

    #[test]
    fn standard_ordering_methods_need_no_recursion_guards() {
        use crate::{compiler::ensure_mir_artifacts, mir::OperationKind};
        let session = CompilerSession::new();
        let std_id = crate::std::STD_MODULE_ID;
        ensure_mir_artifacts(session.raw_modules(), std_id);
        let artifacts = session
            .mir_artifacts_for(std_id, MirOptimization::Disabled)
            .unwrap();
        let module = session.std_module();
        let mut checked = 0;
        for index in 0..module.function_count() {
            let id = LocalFunctionId::from_index(index);
            let Some(name) = module.get_function_name_by_id(id) else {
                continue;
            };
            if !name.contains("Ord<") || !name.contains("#impl:") {
                continue;
            }
            let body = artifacts.get(id).unwrap();
            assert!(
                !body.blocks().any(|block| body
                    .block(block)
                    .operations()
                    .iter()
                    .any(|op| op.kind == OperationKind::CheckCallDepth)),
                "{name}"
            );
            checked += 1;
        }
        assert!(checked > 0, "expected standard Ord implementation methods");
    }

    #[test]
    fn ordinary_helpers_do_not_guard_default_bearing_impls() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Disabled);
        let mir = session.emit_mir(
            "helpers",
            r#"
            fn leaf(x: bool) -> Ordering { if x { Less } else { Greater } }
            fn helper(x: bool) -> Ordering { leaf(x) }
            struct Flag(bool)
            impl Ord for Flag {
                fn cmp(left: Flag, right: Flag) -> Ordering { helper(left.0) }
            }
            fn compare(left: Flag, right: Flag) -> bool { left < right }
        "#,
        );
        assert!(!mir.contains("check_call_depth"), "{mir}");
    }
}
