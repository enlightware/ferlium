use crate::{
    r#type::Type,
    value::{NativeFunction, PrimitiveValue, TypedValue, Value},
};

/// Along with the Rust native stack, corresponds to the Zinc Abstract Machine of Caml language family
#[derive(Default)]
pub struct Context {
    // TODO: revisit pub later on
    // pub stack: Vec<Value>, // Stack is not needed as we are using the Rust native stack
    pub environment: Vec<(Value, Type)>,
}

// TODO: add support for closure conversion (i.e. every function receives its own closure as an extra argument, from which it recovers values for its free variables)

/// A node of the abstract syntax tree
#[derive(Debug)]
pub enum Node {
    Literal(Box<dyn PrimitiveValue>),
    NativeFunctionCall {
        function: Box<dyn NativeFunction>,
        arguments: Vec<Node>,
    },
    EnvStore(Box<Node>),
    EnvLoad(usize),
    BlockExpr(Vec<Node>),
    Project(Box<Node>, usize),
}

impl Node {
    pub fn eval(&self, ctx: &mut Context) -> Value {
        match self {
            Node::Literal(value) => Value::Primitive(value.clone()),
            Node::NativeFunctionCall {
                function,
                arguments,
                ..
            } => {
                let arguments = arguments.iter().map(|arg| arg.eval(ctx)).collect();
                function.call(arguments)
            }
            Node::EnvStore(node) => {
                let value = node.eval(ctx);
                ctx.environment.push((value.clone(), node.ty(ctx)));
                value
            }
            Node::EnvLoad(index) => ctx.environment[*index].0.clone(),
            Node::BlockExpr(nodes) => {
                let env_size = ctx.environment.len();
                let return_value = nodes
                    .iter()
                    .map(|node| node.eval(ctx))
                    .last()
                    .unwrap_or(Value::primitive(()));
                ctx.environment.truncate(env_size);
                return_value
            }
            Node::Project(node, index) => {
                let value = node.eval(ctx);
                match value {
                    Value::List(values) => values[*index].clone(),
                    _ => panic!("Cannot project from a non-list value"),
                }
            }
        }
    }

    pub fn eval_and_print(&self, ctx: &mut Context) {
        let value = self.eval(ctx);
        let ty = self.ty(ctx);
        println!("{}", TypedValue { value, ty });
    }

    pub fn ty(&self, ctx: &Context) -> Type {
        match self {
            Node::Literal(value) => Type::Primitive(value.native_type()),
            Node::NativeFunctionCall { function, .. } => function.ty(),
            Node::EnvStore(node) => node.ty(ctx),
            Node::EnvLoad(index) => ctx.environment[*index].1.clone(),
            Node::BlockExpr(nodes) => nodes
                .last()
                .map(|node| node.ty(ctx))
                .unwrap_or(Type::primitive::<()>()),
            Node::Project(node, index) => {
                let ty = node.ty(ctx);
                match ty {
                    Type::Tuple(types) => types[*index].clone(),
                    Type::Record(fields) => fields[*index].1.clone(),
                    _ => panic!("Cannot project from a non product-type"),
                }
            }
        }
    }
}
