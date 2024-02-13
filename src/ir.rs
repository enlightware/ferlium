use crate::{
    r#type::Type,
    value::{NativeFunction, PrimitiveValue, TypedValue, Value},
};

/// A node of the abstract syntax tree
#[derive(Debug)]
pub enum Node {
    Literal(Box<dyn PrimitiveValue>),
    NativeFunctionCall {
        function: Box<dyn NativeFunction>,
        arguments: Vec<Node>,
    },
}

impl Node {
    pub fn eval(&self) -> Value {
        match self {
            Node::Literal(value) => Value::Primitive(value.clone()),
            Node::NativeFunctionCall {
                function,
                arguments,
                ..
            } => {
                let arguments = arguments.iter().map(|arg| arg.eval()).collect();
                function.call(arguments)
            }
        }
    }

    pub fn eval_and_print(&self) {
        let value = self.eval();
        let ty = self.ty();
        println!("{}", TypedValue { value, ty });
    }

    pub fn ty(&self) -> Type {
        match self {
            Node::Literal(value) => Type::Primitive(value.native_type()),
            Node::NativeFunctionCall { function, .. } => function.ty(),
        }
    }
}
