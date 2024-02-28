use either::Either;
use slotmap::{new_key_type, SlotMap};

use crate::{function::FunctionDescription, r#type::Type, value::Value};

new_key_type! {
    /// A key to a function in the context
    pub struct FunctionKey;
}

pub type Functions = SlotMap<FunctionKey, FunctionDescription>;

/// Along with the Rust native stack, corresponds to the Zinc Abstract Machine of Caml language family
pub struct Context<'a> {
    pub functions: &'a Functions,
    // TODO: revisit pub later on
    // pub stack: Vec<Value>, // Stack is not needed as we are using the Rust native stack
    pub environment: Vec<Value>,
}
impl Context<'_> {
    pub fn new(functions: &Functions) -> Context {
        Context {
            functions,
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
pub struct Pattern(Vec<Either<Type, Value>>);

#[derive(Debug, Clone)]
pub struct Match {
    pub value: Box<Node>,
    pub alternatives: Vec<(Pattern, Node)>,
    pub default: Option<Node>,
}

/// A node of the abstract syntax tree
#[derive(Debug, Clone)]
pub enum Node {
    Literal(Value),
    Apply(Box<Application>),
    StaticApply(Box<StaticApplication>),
    EnvStore(Box<Node>),
    EnvLoad(usize),
    BlockExpr(Vec<Node>),
    Project(Box<Node>, usize),
    Match(Box<Match>),
}

impl Node {
    pub fn eval(&self, ctx: &mut Context) -> Value {
        match self {
            Node::Literal(value) => value.clone(),
            Node::Apply(app) => {
                let arguments = app.arguments.iter().map(|arg| arg.eval(ctx)).collect();
                let key = *app.function.eval(ctx).as_function().unwrap();
                let function = &ctx.functions[key];
                function.code.call(arguments, ctx.functions)
            }
            Node::StaticApply(app) => {
                let arguments = app.arguments.iter().map(|arg| arg.eval(ctx)).collect();
                let function = &ctx.functions[app.function];
                function.code.call(arguments, ctx.functions)
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
            Node::Project(node, index) => {
                let value = node.eval(ctx);
                match value {
                    Value::List(compound) => compound.values[*index].clone(),
                    _ => panic!("Cannot project from a non-compound value"),
                }
            }
            Node::Match(match_) => {
                let value = match_.value.eval(ctx);
                for (pattern, node) in &match_.alternatives {
                    for token in &pattern.0 {
                        match token {
                            Either::Left(ty) => {
                                if value.ty(ctx.functions).can_be_used_in_place_of(ty) {
                                    return node.eval(ctx);
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

    // Note: unclear whether we really need this method
    // pub fn ty(&self, ctx: &Context) -> Type {
    //     match self {
    //         Node::Literal(value) => value.ty(),
    //         Node::Apply(node) => node.function.ty(),
    //         Node::EnvStore(node) => node.ty(ctx),
    //         Node::EnvLoad(index) => ctx.environment[*index].ty(),
    //         Node::BlockExpr(nodes) => nodes
    //             .last()
    //             .map(|node| node.ty(ctx))
    //             .unwrap_or(Type::primitive::<()>()),
    //         Node::Project(node, index) => {
    //             let ty = node.ty(ctx);
    //             match ty {
    //                 Type::Tuple(types) => types[*index].clone(),
    //                 Type::Record(fields) => fields[*index].1.clone(),
    //                 _ => panic!("Cannot project from a non product-type"),
    //             }
    //         }
    //         Node::Match(_) => todo!(),
    //     }
    // }
}
