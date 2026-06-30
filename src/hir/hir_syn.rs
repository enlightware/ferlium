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
    hir::function::PendingArgPassing,
    hir::value::{LiteralNativeValue, LiteralValue},
    hir::{self, CallArgument, HirPhase, NodeId, NodeKind, Project, Variant},
    module::{
        FunctionId, LocalDecl, LocalDeclId, LocalFrameSlot, PendingLocalDrop,
        PendingTakeLocalValueMode, ProjectionIndex, TraitImplId, id::Id,
    },
    std::string::String as FerliumString,
    types::mutability::{MutType, MutVal},
    types::r#type::{FnType, Type},
};
use std::str::FromStr;
use ustr::{Ustr, ustr};

use NodeKind as K;

#[allow(dead_code)]
pub fn native<P: HirPhase, T: LiteralNativeValue + 'static>(value: T) -> NodeKind<P> {
    immediate(LiteralValue::new_native(value))
}

pub fn native_str<P: HirPhase>(value: &str) -> NodeKind<P> {
    immediate(LiteralValue::new_native(
        FerliumString::from_str(value).unwrap(),
    ))
}

pub fn immediate<P: HirPhase>(value: LiteralValue) -> NodeKind<P> {
    K::Immediate(value)
}

pub fn static_apply_with_argument_passing(
    function: FunctionId,
    ty: FnType,
    arguments: impl Into<Vec<NodeId>>,
    argument_passing: Vec<PendingArgPassing>,
    span: Location,
) -> NodeKind {
    let arguments = arguments.into();
    let arguments = CallArgument::from_values_and_passing(arguments, argument_passing);
    K::StaticApply(b(hir::StaticApplication {
        function,
        function_path: None,
        function_span: span,
        extra_arguments: Vec::new(),
        argument_names: (0..arguments.len())
            .map(|i| ustr(&format!("arg{i}")))
            .collect(),
        arguments,
        ty,
        inst_data: hir::FnInstData::none(),
    }))
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

pub fn store_new_local(
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
    local.set_owned_storage(PendingLocalDrop::Unknown);
    local.slot = LocalFrameSlot::from_index(index);
    locals.push(local);
    (K::StoreLocal(hir::StoreLocal { value, id }), id)
}

#[allow(dead_code)]
pub fn store_local_to<P: HirPhase>(value: NodeId<P>, id: LocalDeclId) -> NodeKind<P> {
    K::StoreLocal(hir::StoreLocal { value, id })
}

pub fn get_dictionary(dictionary: TraitImplId) -> NodeKind {
    K::GetDictionary(hir::GetDictionary { dictionary })
}

pub fn load_local<P: HirPhase>(id: LocalDeclId) -> NodeKind<P> {
    K::LoadLocal(hir::LoadLocal { id })
}

pub fn take_local_value(id: LocalDeclId) -> NodeKind {
    K::TakeLocalValue(hir::TakeLocalValue {
        id,
        mode: PendingTakeLocalValueMode::MoveOwned,
    })
}

pub fn project(tuple: NodeId, index: ProjectionIndex) -> NodeKind {
    K::Project(Project::new(tuple, index))
}

pub fn extract_tag(variant: NodeId) -> NodeKind {
    K::ExtractTag(variant)
}

pub fn variant(tag: Ustr, payload: NodeId) -> NodeKind {
    K::Variant(Variant::new(tag, payload))
}

#[allow(dead_code)]
pub fn assign<P: HirPhase>(
    place: NodeId<P>,
    value: NodeId<P>,
    drop: Option<P::LocalDrop>,
) -> NodeKind<P> {
    K::Assign(hir::Assignment { place, value, drop })
}

#[allow(dead_code)]
pub fn return_<P: HirPhase>(value: NodeId<P>) -> NodeKind<P> {
    K::Return(value)
}

#[allow(dead_code)]
pub fn yield_<P: HirPhase>(value: NodeId<P>) -> NodeKind<P> {
    K::Yield(value)
}

#[allow(dead_code)]
pub fn with_yielded<P: HirPhase>(
    accessor: NodeId<P>,
    binding: LocalDeclId,
    body: NodeId<P>,
) -> NodeKind<P> {
    K::WithYielded(hir::WithYielded {
        accessor,
        binding,
        body,
    })
}

#[allow(dead_code)]
pub fn static_apply<P: HirPhase>(
    function: FunctionId,
    ty: FnType,
    arguments: Vec<CallArgument<P>>,
    span: Location,
) -> NodeKind<P> {
    K::StaticApply(b(hir::StaticApplication {
        function,
        function_path: None,
        function_span: span,
        extra_arguments: Vec::new(),
        argument_names: (0..arguments.len())
            .map(|i| ustr(&format!("arg{i}")))
            .collect(),
        arguments,
        ty,
        inst_data: hir::FnInstData::none(),
    }))
}

pub fn tuple<P: HirPhase>(values: impl IntoSVec2<NodeId<P>>) -> NodeKind<P> {
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

pub fn block<P: HirPhase>(statements: impl IntoSVec2<NodeId<P>>) -> NodeKind<P> {
    K::Block(b(hir::Block {
        body: b(statements.into_svec2()),
        cleanup: Vec::new(),
    }))
}

/// Like [`block`], but the listed owned locals are dropped when the block exits.
///
/// Generated HIR that leaves an owned local live at the tail must list it here, or it leaks:
/// synthesized blocks don't get the type-checker's automatic per-scope cleanup.
pub fn block_with_cleanup<P: HirPhase>(
    statements: impl IntoSVec2<NodeId<P>>,
    cleanup: Vec<LocalDeclId>,
) -> NodeKind<P> {
    K::Block(b(hir::Block {
        body: b(statements.into_svec2()),
        cleanup,
    }))
}
