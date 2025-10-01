// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use crate::{
    containers::{b, IntoSVec2},
    effects::EffType,
    ir::{self, Node},
    module::{FunctionId, TraitImplId},
    r#type::FnType,
    std::math::int_type,
    value::{NativeValue, Value},
    Location,
};
use ustr::ustr;

use ir::NodeKind;
use NodeKind as K;

pub fn native<T: NativeValue + 'static>(value: T) -> NodeKind {
    immediate(Value::native(value))
}

pub fn immediate(value: Value) -> NodeKind {
    K::Immediate(ir::Immediate::new(value))
}

pub fn static_apply(
    function: FunctionId,
    ty: FnType,
    span: Location,
    arguments: Vec<Node>,
) -> NodeKind {
    K::StaticApply(b(ir::StaticApplication {
        function,
        function_path: ustr("synthesized"),
        function_span: span,
        argument_names: (0..arguments.len())
            .map(|i| ustr(&format!("arg{i}")))
            .collect(),
        arguments,
        ty,
        inst_data: ir::FnInstData::none(),
    }))
}

pub fn get_dictionary(dictionary: TraitImplId) -> NodeKind {
    K::GetDictionary(ir::GetDictionary { dictionary })
}

pub fn load(index: usize) -> NodeKind {
    K::EnvLoad(b(ir::EnvLoad { index, name: None }))
}

pub fn project(tuple: Node, index: usize) -> NodeKind {
    K::Project(b((tuple, index)))
}

pub fn index_immediate(array: Node, index: isize) -> NodeKind {
    let index_node = Node::new(
        immediate(Value::native(index)),
        int_type(),
        EffType::empty(),
        array.span,
    );
    K::Index(b(array), b(index_node))
}

pub fn extract_tag(variant: Node) -> NodeKind {
    K::ExtractTag(b(variant))
}

pub fn variant(tag: &str, payload: Node) -> NodeKind {
    K::Variant(b((ustr(tag), payload)))
}

pub fn tuple(values: impl IntoSVec2<Node>) -> NodeKind {
    K::Tuple(b(values.into_svec2()))
}

pub fn record(values: impl IntoSVec2<Node>) -> NodeKind {
    K::Record(b(values.into_svec2()))
}

pub fn array(values: impl IntoSVec2<Node>) -> NodeKind {
    K::Array(b(values.into_svec2()))
}

pub fn case(value: Node, alternatives: Vec<(Value, Node)>, default: Node) -> NodeKind {
    K::Case(b(ir::Case {
        value,
        alternatives,
        default,
    }))
}

pub fn case_from_complete_alternatives(
    value: Node,
    mut alternatives: Vec<(Value, Node)>,
) -> NodeKind {
    let default = alternatives.pop().unwrap().1;
    K::Case(b(ir::Case {
        value,
        alternatives,
        default,
    }))
}
