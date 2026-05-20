// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use crate::{
    Location,
    containers::{IntoSVec2, b},
    hir::value::{LiteralNativeValue, LiteralValue},
    hir::{self, NodeArena, NodeId},
    module::{
        FunctionId, LocalClone, LocalDecl, LocalDeclId, LocalFrameSlot, ProjectionIndex,
        TraitImplId, id::Id,
    },
    std::{math::int_type, string::String as FerliumString},
    types::effects::EffType,
    types::mutability::{MutType, MutVal},
    types::r#type::{FnType, Type},
};
use std::str::FromStr;
use ustr::{Ustr, ustr};

use NodeKind as K;
use hir::NodeKind;

#[allow(dead_code)]
pub fn native<T: LiteralNativeValue + 'static>(value: T) -> NodeKind {
    immediate(LiteralValue::new_native(value))
}

pub fn native_str(value: &str) -> NodeKind {
    immediate(LiteralValue::new_native(
        FerliumString::from_str(value).unwrap(),
    ))
}

pub fn immediate(value: LiteralValue) -> NodeKind {
    K::Immediate(hir::Immediate::new(value))
}

pub fn static_apply(
    function: FunctionId,
    ty: FnType,
    arguments: impl Into<Vec<NodeId>>,
    span: Location,
) -> NodeKind {
    let arguments = arguments.into();
    K::StaticApply(b(hir::StaticApplication {
        function,
        function_path: None,
        function_span: span,
        argument_names: (0..arguments.len())
            .map(|i| ustr(&format!("arg{i}")))
            .collect(),
        arguments,
        ty,
        inst_data: hir::FnInstData::none(),
    }))
}

pub fn static_apply_pure(
    function: FunctionId,
    arguments: impl IntoIterator<Item = (NodeId, Type)>,
    ret_ty: Type,
    span: Location,
) -> NodeKind {
    let (arguments, args_tys): (Vec<_>, Vec<_>) = arguments.into_iter().unzip();
    static_apply(
        function,
        FnType::new_by_val(args_tys, ret_ty, EffType::empty()),
        arguments,
        span,
    )
}

pub fn local(name: &str, ty: Type) -> LocalDecl {
    LocalDecl::new(
        (ustr(name), Location::new_synthesized()),
        MutType::constant(),
        ty,
        None,
        Location::new_synthesized(),
    )
}

pub fn store_new(
    value: NodeId,
    index: usize,
    name: &str,
    mutable: MutVal,
    ty: Type,
    locals: &mut Vec<LocalDecl>,
) -> (NodeKind, LocalDeclId) {
    let id = LocalDeclId::from_index(locals.len());
    let mut local = LocalDecl::new(
        (ustr(name), Location::new_synthesized()),
        MutType::resolved(mutable),
        ty,
        None,
        Location::new_synthesized(),
    );
    local.owns_storage = true;
    local.slot = LocalFrameSlot::from_index(index);
    locals.push(local);
    (K::EnvStore(hir::EnvStore { value, id }), id)
}

#[allow(dead_code)]
pub fn store_to(value: NodeId, id: LocalDeclId) -> NodeKind {
    K::EnvStore(hir::EnvStore { value, id })
}

pub fn get_dictionary(dictionary: TraitImplId) -> NodeKind {
    K::GetDictionary(hir::GetDictionary { dictionary })
}

pub fn load(id: LocalDeclId) -> NodeKind {
    K::EnvLoad(hir::EnvLoad { id })
}

pub fn move_local(id: LocalDeclId) -> NodeKind {
    K::EnvMove(hir::EnvMove { id })
}

pub fn project(tuple: NodeId, index: ProjectionIndex) -> NodeKind {
    K::Project(tuple, index)
}

/// Build an array indexing place node for generated HIR.
pub fn index_immediate(arena: &mut NodeArena, array: NodeId, index: isize) -> NodeKind {
    let array_span = arena[array].span;
    let index_node = arena.alloc(hir::Node::new(
        immediate(LiteralValue::new_native(index)),
        int_type(),
        EffType::empty(),
        array_span,
    ));
    K::Index(hir::ArrayIndex {
        array,
        index: index_node,
    })
}

/// Build an owned array indexing node for generated HIR.
pub fn index_immediate_clone(
    arena: &mut NodeArena,
    array: NodeId,
    index: isize,
    clone: LocalClone,
    element_ty: Type,
) -> NodeKind {
    let span = arena[array].span;
    let index = index_immediate(arena, array, index);
    let index_place = arena.alloc(hir::Node::new(index, element_ty, EffType::empty(), span));
    K::ValueClone(hir::ValueClone {
        source: index_place,
        clone: Some(clone),
    })
}

pub fn extract_tag(variant: NodeId) -> NodeKind {
    K::ExtractTag(variant)
}

pub fn variant(tag: Ustr, payload: NodeId) -> NodeKind {
    K::Variant(tag, payload)
}

pub fn tuple(values: impl IntoSVec2<NodeId>) -> NodeKind {
    K::Tuple(b(values.into_svec2()))
}

pub fn record(values: impl IntoSVec2<NodeId>) -> NodeKind {
    K::Record(b(values.into_svec2()))
}

pub fn array(values: impl IntoSVec2<NodeId>) -> NodeKind {
    K::Array(b(values.into_svec2()))
}

pub fn case(value: NodeId, alternatives: Vec<(LiteralValue, NodeId)>, default: NodeId) -> NodeKind {
    K::Case(b(hir::Case {
        value,
        alternatives,
        default,
    }))
}

pub fn case_from_complete_alternatives(
    value: NodeId,
    mut alternatives: Vec<(LiteralValue, NodeId)>,
) -> NodeKind {
    let default = alternatives.pop().unwrap().1;
    K::Case(b(hir::Case {
        value,
        alternatives,
        default,
    }))
}

pub fn block(statements: impl IntoSVec2<NodeId>) -> NodeKind {
    K::Block(b(statements.into_svec2()))
}
