use crate::{
    containers::{b, IntoSVec2},
    function::FunctionRef,
    ir::{self, Node},
    r#type::FnType,
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
    function: FunctionRef,
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

pub fn load(index: usize) -> NodeKind {
    K::EnvLoad(b(ir::EnvLoad { index, name: None }))
}

pub fn project(tuple: Node, index: usize) -> NodeKind {
    K::Project(b((tuple, index)))
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

pub fn array(values: impl IntoSVec2<Node>) -> NodeKind {
    K::Array(b(values.into_svec2()))
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
