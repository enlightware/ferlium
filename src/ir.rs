use either::Either;
use ustr::Ustr;

use crate::{
    containers::{SmallVec1, SmallVec2},
    function::FunctionKey,
    value::Value,
};

/// Along with the Rust native stack, corresponds to the Zinc Abstract Machine of Caml language family
pub struct Context {
    // TODO: revisit pub later on
    // pub stack: Vec<Value>, // Stack is not needed as we are using the Rust native stack
    pub environment: Vec<Value>,
}
impl Context {
    #[allow(clippy::new_without_default)]
    pub fn new() -> Context {
        Context {
            environment: Vec::new(),
        }
    }
}

// TODO: later, handle tail optimisation in a special way

#[derive(Debug, Clone)]
pub struct Application {
    pub function: Node,
    pub arguments: Vec<Node>,
}

#[derive(Debug, Clone)]
pub struct StaticApplication {
    pub function: FunctionKey,
    pub arguments: Vec<Node>,
}

#[derive(Debug, Clone)]
pub struct Pattern(SmallVec1<Either<Ustr, Value>>);

// TODO: allow to match more than one expression
// TODO: allow to deconstruct variant, record, tuple
#[derive(Debug, Clone)]
pub struct Match {
    pub value: Node,
    pub alternatives: SmallVec1<(Pattern, Node)>,
    pub default: Option<Box<Node>>,
}

/// A node of the execution tree
#[derive(Debug, Clone)]
pub enum Node {
    Literal(Value),
    BuildTuple(Box<SmallVec2<Node>>),
    Project(Box<(Node, usize)>),
    Apply(Box<Application>),
    StaticApply(Box<StaticApplication>),
    EnvStore(Box<Node>),
    EnvLoad(usize),
    BlockExpr(Box<SmallVec2<Node>>),
    Match(Box<Match>),
}

impl Node {
    pub fn eval(&self, ctx: &mut Context) -> Value {
        match self {
            Node::Literal(value) => value.clone(),
            Node::BuildTuple(nodes) => {
                let values = nodes.iter().map(|node| node.eval(ctx)).collect();
                Value::Tuple(Box::new(values))
            }
            Node::Project(node_and_index) => {
                let value = node_and_index.0.eval(ctx);
                match value {
                    Value::Tuple(tuple) => tuple[node_and_index.1].clone(),
                    Value::Variant(variant) => variant.value.clone(),
                    _ => panic!("Cannot project from a non-compound value"),
                }
            }
            Node::Apply(app) => {
                let arguments = app.arguments.iter().map(|arg| arg.eval(ctx)).collect();
                let function_value = app.function.eval(ctx);
                let function = function_value.as_function().unwrap().get();
                function.code.call(arguments, &())
            }
            Node::StaticApply(app) => {
                let arguments = app.arguments.iter().map(|arg| arg.eval(ctx)).collect();
                let function = app.function.get();
                function.code.call(arguments, &())
            }
            Node::EnvStore(node) => {
                let value = node.eval(ctx);
                ctx.environment.push(value.clone());
                value
            }
            Node::EnvLoad(index) => ctx.environment[*index].clone(),
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
            Node::Match(match_) => {
                let value = match_.value.eval(ctx);
                for (pattern, node) in &match_.alternatives {
                    for token in &pattern.0 {
                        match token {
                            Either::Left(tag) => {
                                if let Value::Variant(variant) = &value {
                                    if variant.tag == *tag {
                                        return node.eval(ctx);
                                    }
                                }
                            }
                            Either::Right(v) => {
                                if *v == value {
                                    return node.eval(ctx);
                                }
                            }
                        }
                    }
                }
                if let Some(default) = &match_.default {
                    default.eval(ctx)
                } else {
                    panic!("No match found for value {:?}", value);
                }
            }
        }
    }

    pub fn eval_and_print(&self, ctx: &mut Context) {
        let value = self.eval(ctx);
        println!("{}", value);
    }
}
