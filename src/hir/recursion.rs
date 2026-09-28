// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! One call graph for finalized functions, including calls hidden by value operations.
//! Known cycles and unresolved dispatch both need runtime checks, but only known cycles
//! prevent inlining. Inlining an unresolved dispatch must retain its check.

use crate::{
    FxHashSet, Modules,
    graph::find_strongly_connected_components,
    hir::{
        self, ENodeId, NodeKind,
        dictionary::{EvidenceBindingSource, StaticEvidence},
    },
    module::{
        EvidenceBindingId, FunctionId, Module, ModuleEnv, ModuleFunction, ResolvedLocalClone,
        ResolvedLocalDrop, ResolvedTakeLocalValueMode, TraitDictionaryEntry, TraitDictionaryId,
        id::Id,
    },
    std::value::{VALUE_CLONE_METHOD_INDEX, VALUE_DROP_METHOD_INDEX},
    types::{effects::EffType, r#trait::TraitDictionaryEntryIndex, r#type::Type},
};

#[derive(Default)]
struct Calls {
    local: Vec<usize>,
    unresolved: bool,
}

impl crate::graph::Node for Calls {
    type Index = usize;

    fn neighbors(&self) -> impl Iterator<Item = usize> {
        self.local.iter().copied()
    }
}

struct Collector<'a> {
    env: ModuleEnv<'a>,
    function: &'a ModuleFunction,
    first_function: usize,
    calls: Calls,
}

impl Collector<'_> {
    fn call(&mut self, target: FunctionId) {
        if target.module == self.env.current.module_id()
            && let Some(index) = target.function.as_index().checked_sub(self.first_function)
        {
            self.calls.local.push(index);
        }
        let function = self
            .env
            .module_by_id(target.module)
            .and_then(|module| module.get_function_by_id(target.function));
        // Typed native entries promise not to re-enter the current execution.
        // Other host callbacks may do so and require a check in their caller.
        if function.is_none_or(|function| {
            function.code.as_script().is_none() && function.code.native_entry().is_none()
        }) {
            self.calls.unresolved = true;
        }
    }

    fn dictionary(&self, node: ENodeId) -> Option<TraitDictionaryId> {
        match &self.env.current.hir_arena[node].kind {
            NodeKind::GetDictionary(value) => Some(TraitDictionaryId::new(
                value.dictionary.module,
                value.dictionary.impl_id,
            )),
            NodeKind::LoadDictionary(value) => self.binding(value.extra_parameter),
            _ => None,
        }
    }

    fn binding(&self, id: EvidenceBindingId) -> Option<TraitDictionaryId> {
        match &self.function.evidence_bindings[id.as_index()].source {
            EvidenceBindingSource::Static(StaticEvidence::Dictionary { definition, .. })
            | EvidenceBindingSource::ConstructedDictionary { definition, .. } => Some(*definition),
            _ => None,
        }
    }

    fn entry(&mut self, dictionary: Option<TraitDictionaryId>, index: TraitDictionaryEntryIndex) {
        let target = dictionary.and_then(|id| {
            let module = self.env.module_by_id(id.module_id)?;
            let dictionary = &module.get_impl_data(id.impl_id)?.dictionary_value;
            let TraitDictionaryEntry::Function(function) = dictionary.entry(index);
            Some(FunctionId::new(id.module_id, function))
        });
        if let Some(target) = target {
            self.call(target);
        } else {
            self.calls.unresolved = true;
        }
    }

    fn clone_value(&mut self, clone: ResolvedLocalClone) {
        match clone {
            ResolvedLocalClone::TrivialCopy => {}
            ResolvedLocalClone::Static(function) => self.call(function),
            ResolvedLocalClone::Dictionary(binding) => self.entry(
                self.binding(binding),
                TraitDictionaryEntryIndex::from_index(VALUE_CLONE_METHOD_INDEX.as_index()),
            ),
        }
    }

    fn drop_value(&mut self, drop: ResolvedLocalDrop) {
        match drop {
            ResolvedLocalDrop::Skip => {}
            ResolvedLocalDrop::Static(function) => self.call(function),
            ResolvedLocalDrop::Dictionary(binding) => self.entry(
                self.binding(binding),
                TraitDictionaryEntryIndex::from_index(VALUE_DROP_METHOD_INDEX.as_index()),
            ),
        }
    }

    fn node(&mut self, id: ENodeId) {
        let node = &self.env.current.hir_arena[id];
        match &node.kind {
            NodeKind::StaticApply(call) => self.call(call.function),
            NodeKind::CallDictionaryFunction(call) => {
                self.entry(self.dictionary(call.dictionary), call.entry_index)
            }
            NodeKind::FunctionApply(call) => {
                match &self.env.current.hir_arena[call.function].kind {
                    NodeKind::GetFunction(function) => self.call(function.function),
                    NodeKind::GetDictionaryFunction(function) => {
                        self.entry(self.dictionary(function.dictionary), function.entry_index)
                    }
                    _ => self.calls.unresolved = true,
                }
            }
            NodeKind::SubscriptApply(_)
            | NodeKind::CloneClosureEnv(_)
            | NodeKind::DropClosureEnv(_)
            | NodeKind::CloneSubscriptValue(_)
            | NodeKind::DropSubscriptValue(_) => self.calls.unresolved = true,
            NodeKind::CloneValue(value) => self.clone_value(value.clone),
            NodeKind::TakeLocalValue(value) => {
                if let ResolvedTakeLocalValueMode::CloneBorrowed(clone) = value.mode {
                    self.clone_value(clone);
                }
            }
            NodeKind::DropValue(value) => self.drop_value(value.drop),
            NodeKind::Assign(value) => {
                if let Some(drop) = value.drop {
                    self.drop_value(drop);
                }
            }
            NodeKind::Block(block) => {
                for local in &block.cleanup {
                    if let Some(drop) = self.function.locals[local.as_index()].local_drop() {
                        self.drop_value(*drop);
                    }
                }
            }
            NodeKind::Uninit
            | NodeKind::Immediate(_)
            | NodeKind::Tuple(_)
            | NodeKind::Record(_)
            | NodeKind::Array(_)
            | NodeKind::Variant(_)
            | NodeKind::BuildClosure(_)
            | NodeKind::Project(_)
            | NodeKind::LoadLocal(_)
            | NodeKind::StoreLocal(_)
            | NodeKind::BuildSubscriptValue(_)
            | NodeKind::GetFunction(_)
            | NodeKind::GetSubscript(_)
            | NodeKind::GetDictionary(_)
            | NodeKind::LoadDictionary(_)
            | NodeKind::LoadSubscriptEvidence(_)
            | NodeKind::LoadVariantPayloadStorageEvidence(_)
            | NodeKind::GetDictionaryFunction(_)
            | NodeKind::CheckCallDepth
            | NodeKind::CheckFuel
            | NodeKind::Return(_)
            | NodeKind::Yield(_)
            | NodeKind::WithYielded(_)
            | NodeKind::WithPlace(_)
            | NodeKind::Case(_)
            | NodeKind::Loop(_)
            | NodeKind::Break(_)
            | NodeKind::Continue(_) => {}
            NodeKind::FieldAccess(never)
            | NodeKind::PendingAssignment(never)
            | NodeKind::TraitMethodApply(never)
            | NodeKind::GetTraitMethod(never)
            | NodeKind::GetTraitAssociatedConst(never)
            | NodeKind::GetTraitDictionary(never) => match *never {},
        }
    }
}

/// Run after elaboration has resolved ownership dispatch and dictionary bindings.
/// Imported modules already guard their own cycles and unresolved dispatch. They cannot
/// acquire new static edges back into this module; such callbacks cross a guarded boundary.
pub(crate) fn guard_module(module: &mut Module, others: &Modules) {
    guard_functions_from(module, others, 0);
}

/// Previously finalized functions cannot refer to newly appended function identities.
/// Analyze only the appended suffix when expression emission extends a checked module.
pub(super) fn guard_functions_from(module: &mut Module, others: &Modules, first_function: usize) {
    let calls = module
        .functions
        .iter()
        .skip(first_function)
        .map(|function| {
            let mut collector = Collector {
                env: ModuleEnv::new(module, others),
                function,
                first_function,
                calls: Calls::default(),
            };
            if let Some(script) = function.code.as_script() {
                let mut pending = vec![script.entry_node_id];
                let mut visited = FxHashSet::default();
                while let Some(id) = pending.pop() {
                    if visited.insert(id) {
                        collector.node(id);
                        pending.extend(module.hir_arena[id].kind.child_node_ids());
                    }
                }
            }
            collector.calls.local.sort_unstable();
            collector.calls.local.dedup();
            collector.calls
        })
        .collect::<Vec<_>>();
    let mut recursive = vec![false; calls.len()];
    for component in find_strongly_connected_components(&calls) {
        if component.len() > 1 || calls[component[0]].local.contains(&component[0]) {
            for index in component {
                recursive[index] = true;
            }
        }
    }
    for (index, calls) in calls.iter().enumerate() {
        let Some(script) = module.functions[first_function + index]
            .code
            .as_script_mut()
        else {
            continue;
        };
        script.recursive = recursive[index];
        if !recursive[index] && !calls.unresolved {
            continue;
        }
        let root = script.entry_node_id;
        let arena = &mut module.hir_arena;
        if matches!(&arena[root].kind, NodeKind::Block(block)
            if block.body.first().is_some_and(|id| matches!(arena[*id].kind, NodeKind::CheckCallDepth)))
        {
            continue;
        }
        let node = &arena[root];
        let (ty, effects, span) = (node.ty, node.effects.clone(), node.span);
        let check = arena.alloc(hir::Node::new(
            NodeKind::CheckCallDepth,
            Type::unit(),
            EffType::empty(),
            span,
        ));
        script.entry_node_id = arena.alloc(hir::Node::new(
            hir::hir_syn::block(vec![check, root]),
            ty,
            effects,
            span,
        ));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CompilerSession, MirOptimization, module::LocalFunctionId};

    #[test]
    fn guards_do_not_classify_unresolved_callbacks_as_known_recursion() {
        let mut session = CompilerSession::new();
        let output = session.compile(
            "fn apply(f: (int) -> int, x: int) -> int { f(x) } fn cycle(x: int) -> int { cycle(x) }",
            "recursion", crate::module::Path::single_str("recursion"),
        ).unwrap();
        let module = session.expect_fresh_module(output.module_id);
        for (name, recursive) in [("apply", false), ("cycle", true)] {
            let script = module
                .get_function(ustr::ustr(name))
                .unwrap()
                .code
                .as_script()
                .unwrap();
            assert_eq!(script.recursive, recursive, "{name}");
            let NodeKind::Block(block) = &module.hir_arena[script.entry_node_id].kind else {
                panic!("{name} must have a guarded entry");
            };
            assert!(matches!(
                module.hir_arena[block.body[0]].kind,
                NodeKind::CheckCallDepth
            ));
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
