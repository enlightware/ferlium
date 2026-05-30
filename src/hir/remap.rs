// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use crate::{
    FxHashMap,
    containers::SVec2,
    hir::{self, CallArgument, NodeKind, UNode, UNodeArena, UNodeId, UNodeKind, Unelaborated},
};

/// Copy one unelaborated HIR tree into a fresh arena, returning the source-to-destination remap.
pub(crate) fn clone_hir_tree_with_remap(
    src: &UNodeArena,
    root: UNodeId,
) -> (UNodeArena, UNodeId, FxHashMap<UNodeId, UNodeId>) {
    let mut dst = UNodeArena::default();
    let mut remap = FxHashMap::default();
    let root = clone_hir_node(src, &mut dst, &mut remap, root);
    (dst, root, remap)
}

fn clone_hir_node(
    src: &UNodeArena,
    dst: &mut UNodeArena,
    remap: &mut FxHashMap<UNodeId, UNodeId>,
    old: UNodeId,
) -> UNodeId {
    if let Some(&new) = remap.get(&old) {
        return new;
    }
    let old_node = &src[old];
    let kind = clone_hir_kind(src, dst, remap, &old_node.kind);
    let new = dst.alloc(UNode::new(
        kind,
        old_node.ty,
        old_node.effects.clone(),
        old_node.span,
    ));
    remap.insert(old, new);
    new
}

fn clone_hir_node_list(
    src: &UNodeArena,
    dst: &mut UNodeArena,
    remap: &mut FxHashMap<UNodeId, UNodeId>,
    nodes: &[UNodeId],
) -> Vec<UNodeId> {
    nodes
        .iter()
        .map(|&node| clone_hir_node(src, dst, remap, node))
        .collect()
}

fn clone_hir_call_args(
    src: &UNodeArena,
    dst: &mut UNodeArena,
    remap: &mut FxHashMap<UNodeId, UNodeId>,
    args: &[CallArgument<Unelaborated>],
) -> Vec<CallArgument<Unelaborated>> {
    args.iter()
        .map(|arg| CallArgument {
            value: clone_hir_node(src, dst, remap, arg.value),
            passing: arg.passing,
        })
        .collect()
}

fn clone_hir_kind(
    src: &UNodeArena,
    dst: &mut UNodeArena,
    remap: &mut FxHashMap<UNodeId, UNodeId>,
    kind: &UNodeKind,
) -> UNodeKind {
    use NodeKind::*;

    match kind {
        Uninit => Uninit,
        Immediate(value) => Immediate(value.clone()),
        Tuple(nodes) => Tuple(Box::new(SVec2::from_vec(clone_hir_node_list(
            src, dst, remap, nodes,
        )))),
        Record(nodes) => Record(Box::new(SVec2::from_vec(clone_hir_node_list(
            src, dst, remap, nodes,
        )))),
        Array(nodes) => Array(Box::new(SVec2::from_vec(clone_hir_node_list(
            src, dst, remap, nodes,
        )))),
        Variant(node) => Variant(hir::Variant {
            tag: node.tag,
            payload: clone_hir_node(src, dst, remap, node.payload),
        }),
        BuildClosure(node) => BuildClosure(Box::new(hir::BuildClosure {
            function: clone_hir_node(src, dst, remap, node.function),
            dictionary_captures: clone_hir_node_list(src, dst, remap, &node.dictionary_captures),
            captures: clone_hir_node_list(src, dst, remap, &node.captures),
            captures_value_dictionary: node
                .captures_value_dictionary
                .map(|node| clone_hir_node(src, dst, remap, node)),
        })),
        Project(node) => Project(hir::Project {
            value: clone_hir_node(src, dst, remap, node.value),
            index: node.index,
        }),
        FieldAccess(node) => FieldAccess(hir::FieldAccess {
            value: clone_hir_node(src, dst, remap, node.value),
            field: node.field,
        }),
        ProjectAt(node) => ProjectAt(hir::ProjectAt {
            value: clone_hir_node(src, dst, remap, node.value),
            index: node.index,
        }),
        ExtractTag(node) => ExtractTag(clone_hir_node(src, dst, remap, *node)),
        LoadLocal(node) => LoadLocal(*node),
        StoreLocal(node) => StoreLocal(hir::StoreLocal {
            value: clone_hir_node(src, dst, remap, node.value),
            id: node.id,
        }),
        TakeLocalValue(node) => TakeLocalValue(hir::TakeLocalValue {
            id: node.id,
            mode: node.mode,
        }),
        Assign(node) => Assign(hir::Assignment {
            place: clone_hir_node(src, dst, remap, node.place),
            value: clone_hir_node(src, dst, remap, node.value),
            drop: node.drop,
        }),
        CloneValue(node) => CloneValue(hir::CloneValue {
            source: clone_hir_node(src, dst, remap, node.source),
            clone: node.clone,
        }),
        CloneClosureEnv(node) => CloneClosureEnv(hir::CloneClosureEnv {
            source: clone_hir_node(src, dst, remap, node.source),
            target: clone_hir_node(src, dst, remap, node.target),
        }),
        DropClosureEnv(node) => DropClosureEnv(hir::DropClosureEnv {
            target: clone_hir_node(src, dst, remap, node.target),
        }),
        GetFunction(node) => GetFunction(node.clone()),
        Apply(node) => Apply(Box::new(hir::Application {
            function: clone_hir_node(src, dst, remap, node.function),
            arguments: clone_hir_call_args(src, dst, remap, &node.arguments),
            returns_place: node.returns_place,
        })),
        StaticApply(node) => StaticApply(Box::new(hir::StaticApplication {
            function: node.function,
            function_path: node.function_path.clone(),
            function_span: node.function_span,
            extra_arguments: clone_hir_node_list(src, dst, remap, &node.extra_arguments),
            arguments: clone_hir_call_args(src, dst, remap, &node.arguments),
            argument_names: node.argument_names.clone(),
            ty: node.ty.clone(),
            inst_data: node.inst_data.clone(),
            returns_place: node.returns_place,
        })),
        TraitMethodApply(node) => TraitMethodApply(Box::new(hir::TraitMethodApplication {
            trait_id: node.trait_id,
            method_index: node.method_index,
            method_path: node.method_path.clone(),
            method_span: node.method_span,
            arguments: clone_hir_call_args(src, dst, remap, &node.arguments),
            arguments_unnamed: node.arguments_unnamed,
            ty: node.ty.clone(),
            input_tys: node.input_tys.clone(),
            inst_data: node.inst_data.clone(),
        })),
        GetTraitMethod(node) => GetTraitMethod(node.clone()),
        GetTraitAssociatedConst(node) => GetTraitAssociatedConst(node.clone()),
        GetTraitDictionary(node) => GetTraitDictionary(node.clone()),
        GetDictionary(node) => GetDictionary(*node),
        LoadDictionary(node) => LoadDictionary(*node),
        LoadFieldIndex(node) => LoadFieldIndex(*node),
        GetDictionaryMethod(node) => GetDictionaryMethod(hir::GetDictionaryMethod {
            dictionary: clone_hir_node(src, dst, remap, node.dictionary),
            entry_index: node.entry_index,
        }),
        GetDictionaryAssociatedConst(node) => {
            GetDictionaryAssociatedConst(hir::GetDictionaryAssociatedConst {
                dictionary: clone_hir_node(src, dst, remap, node.dictionary),
                entry_index: node.entry_index,
            })
        }
        CallDictionaryMethod(node) => CallDictionaryMethod(Box::new(hir::CallDictionaryMethod {
            dictionary: clone_hir_node(src, dst, remap, node.dictionary),
            entry_index: node.entry_index,
            arguments: clone_hir_call_args(src, dst, remap, &node.arguments),
            ty: node.ty.clone(),
        })),
        CheckCallDepth => CheckCallDepth,
        CheckFuel => CheckFuel,
        Block(node) => Block(Box::new(hir::Block {
            body: Box::new(SVec2::from_vec(clone_hir_node_list(
                src, dst, remap, &node.body,
            ))),
            cleanup: node.cleanup.clone(),
        })),
        Return(node) => Return(clone_hir_node(src, dst, remap, *node)),
        Case(node) => Case(Box::new(hir::Case {
            value: clone_hir_node(src, dst, remap, node.value),
            alternatives: node
                .alternatives
                .iter()
                .map(|(literal, node)| (literal.clone(), clone_hir_node(src, dst, remap, *node)))
                .collect(),
            default: clone_hir_node(src, dst, remap, node.default),
        })),
        Loop(node) => Loop(clone_hir_node(src, dst, remap, *node)),
        SoftBreak => SoftBreak,
    }
}
