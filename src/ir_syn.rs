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
    effects::EffType,
    ir::{self, NodeArena, NodeId},
    module::{FunctionId, LocalDecl, LocalDeclId, TraitImplId, id::Id},
    mutability::{MutType, MutVal},
    std::{math::int_type, string::string_value},
    r#type::{FnType, Type},
    value::{NativeValue, Value},
};
use ustr::{Ustr, ustr};

use NodeKind as K;
use ir::NodeKind;

#[allow(dead_code)]
pub fn native<T: NativeValue + 'static>(value: T) -> NodeKind {
    immediate(Value::native(value))
}

pub fn native_str(value: &str) -> NodeKind {
    immediate(string_value(value))
}

pub fn immediate(value: Value) -> NodeKind {
    K::Immediate(ir::Immediate::new(value))
}

pub fn static_apply(
    function: FunctionId,
    ty: FnType,
    arguments: impl Into<Vec<NodeId>>,
    span: Location,
) -> NodeKind {
    let arguments = arguments.into();
    K::StaticApply(b(ir::StaticApplication {
        function,
        function_path: None,
        function_span: span,
        argument_names: (0..arguments.len())
            .map(|i| ustr(&format!("arg{i}")))
            .collect(),
        arguments,
        ty,
        inst_data: ir::FnInstData::none(),
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
    let local = LocalDecl::new(
        (ustr(name), Location::new_synthesized()),
        MutType::resolved(mutable),
        ty,
        None,
        Location::new_synthesized(),
    );
    locals.push(local);
    (
        K::EnvStore(ir::EnvStore {
            value,
            index: index as u32,
            id,
        }),
        id,
    )
}

#[allow(dead_code)]
pub fn store_to(value: NodeId, index: usize, id: LocalDeclId) -> NodeKind {
    K::EnvStore(ir::EnvStore {
        value,
        index: index as u32,
        id,
    })
}

pub fn get_dictionary(dictionary: TraitImplId) -> NodeKind {
    K::GetDictionary(ir::GetDictionary { dictionary })
}

pub fn load(index: usize, id: LocalDeclId) -> NodeKind {
    K::EnvLoad(ir::EnvLoad {
        index: index as u32,
        id,
    })
}

pub fn project(tuple: NodeId, index: usize) -> NodeKind {
    K::Project(tuple, index)
}

pub fn index_immediate(arena: &mut NodeArena, array: NodeId, index: isize) -> NodeKind {
    let array_span = arena[array].span;
    let index_node = arena.alloc(ir::Node::new(
        immediate(Value::native(index)),
        int_type(),
        EffType::empty(),
        array_span,
    ));
    K::Index(array, index_node)
}

pub fn extract_tag(variant: NodeId) -> NodeKind {
    K::ExtractTag(variant)
}

pub fn variant(tag: Ustr, payload: NodeId) -> NodeKind {
    K::Variant(tag, payload)
}

pub fn unit_variant(tag: Ustr) -> NodeKind {
    immediate(Value::unit_variant(tag))
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

pub fn case(value: NodeId, alternatives: Vec<(Value, NodeId)>, default: NodeId) -> NodeKind {
    K::Case(b(ir::Case {
        value,
        alternatives,
        default,
    }))
}

pub fn case_from_complete_alternatives(
    value: NodeId,
    mut alternatives: Vec<(Value, NodeId)>,
) -> NodeKind {
    let default = alternatives.pop().unwrap().1;
    K::Case(b(ir::Case {
        value,
        alternatives,
        default,
    }))
}

pub fn block(statements: impl IntoSVec2<NodeId>) -> NodeKind {
    K::Block(b(statements.into_svec2()))
}
