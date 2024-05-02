use crate::{
    containers::{SVec1, SVec2, B},
    error::RuntimeError,
    function::FunctionRef,
    r#type::FnArgType,
    std::array,
    value::{ValOrMut, Value},
};

/// Along with the Rust native stack, corresponds to the Zinc Abstract Machine of Caml language family
/// with the addition of Mutable Value Semantics through references to earlier stack frames
pub struct EvalCtx {
    /// all values of all stack frames
    pub environment: Vec<Value>,
    /// base of current stack frame in `environment`
    pub frame_base: usize,
}
impl EvalCtx {
    #[allow(clippy::new_without_default)]
    pub fn new() -> EvalCtx {
        EvalCtx {
            environment: Vec::new(),
            frame_base: 0,
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
    pub function: FunctionRef,
    pub arguments: Vec<Node>,
}

/// A place in the environment (absolute position), with a path to a compound value
/// This behaves like a global address to a Value given our Mutable Value Semantics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Place {
    // index of target variable, absolute in the environment, to allow to access parent frames
    pub target: usize,
    // path within the compound value located at `target`
    pub path: Vec<isize>,
}
impl Place {
    pub fn target_ref<'c>(&self, ctx: &'c mut EvalCtx) -> Result<&'c mut Value, RuntimeError> {
        let mut target = &mut ctx.environment[self.target];
        for &index in &self.path {
            use Value::*;
            target = match target {
                Tuple(tuple) => tuple.get_mut(index as usize).unwrap(),
                Native(primitive) => {
                    // iif the primitive is our standard Array, we can access its elements
                    let array = primitive
                        .as_mut_any()
                        .downcast_mut::<array::Array>()
                        .unwrap();
                    let len = array.len();
                    match array.get_mut_signed(index) {
                        Some(target) => target,
                        None => return Err(RuntimeError::ArrayAccessOutOfBounds { index, len }),
                    }
                }
                _ => panic!("Cannot access a non-compound value"),
            };
        }
        Ok(target)
    }
}

#[derive(Debug, Clone)]
pub struct Assignment {
    pub place: Node,
    pub value: Node,
}

#[derive(Debug, Clone)]
pub struct Case {
    pub value: Node,
    pub alternatives: SVec1<(Value, Node)>,
    pub default: Node,
}

/// The result of evaluating an IR node
pub type EvalResult = Result<Value, RuntimeError>;

/// A node of the expression-based execution tree
#[derive(Debug, Clone)]
pub enum Node {
    Literal(Value),
    Apply(B<Application>),
    StaticApply(B<StaticApplication>),
    EnvStore(B<Node>),
    EnvLoad(usize),
    BlockExpr(B<SVec2<Node>>),
    Assign(B<Assignment>),
    Tuple(B<SVec2<Node>>),
    Project(B<(Node, usize)>),
    Array(B<SVec2<Node>>),
    Index(B<Node>, B<Node>),
    Case(B<Case>),
}

impl Node {
    pub fn format_ind(&self, f: &mut std::fmt::Formatter, indent: usize) -> std::fmt::Result {
        let indent_str = "  ".repeat(indent);
        use Node::*;
        match self {
            Literal(value) => writeln!(f, "{indent_str}{value}"),
            Apply(app) => {
                writeln!(f, "{indent_str}eval")?;
                app.function.format_ind(f, indent + 1)?;
                writeln!(f, "{indent_str}and apply to (")?;
                for arg in &app.arguments {
                    arg.format_ind(f, indent + 1)?;
                }
                writeln!(f, "{indent_str})")
            }
            StaticApply(app) => {
                write!(f, "{indent_str}apply ")?;
                match app.function.get().try_borrow() {
                    Ok(descr) => writeln!(f, "{indent_str}{:p}", descr.code)?,
                    Err(_) => writeln!(f, "{indent_str}self")?,
                }
                writeln!(f, " to (")?;
                for arg in &app.arguments {
                    arg.format_ind(f, indent + 1)?;
                }
                writeln!(f, "{indent_str})")
            }
            EnvStore(node) => {
                writeln!(f, "{indent_str}push")?;
                node.format_ind(f, indent + 1)
            }
            EnvLoad(index) => writeln!(f, "{indent_str}load {index}"),
            BlockExpr(nodes) => {
                for node in nodes.iter() {
                    node.format_ind(f, indent)?;
                }
                Ok(())
            }
            Assign(assignment) => {
                writeln!(f, "{indent_str}assign")?;
                assignment.place.format_ind(f, indent + 1)?;
                assignment.value.format_ind(f, indent + 1)
            }
            Tuple(nodes) => {
                writeln!(f, "{indent_str}tuple")?;
                for node in nodes.iter() {
                    node.format_ind(f, indent + 1)?;
                }
                Ok(())
            }
            Project(projection) => {
                writeln!(f, "{indent_str}project")?;
                projection.0.format_ind(f, indent + 1)?;
                writeln!(f, "{indent_str}at {index}", index = projection.1)
            }
            Array(nodes) => {
                writeln!(f, "{indent_str}array")?;
                for node in nodes.iter() {
                    node.format_ind(f, indent + 1)?;
                }
                Ok(())
            }
            Index(array, index) => {
                writeln!(f, "{indent_str}index")?;
                array.format_ind(f, indent + 1)?;
                index.format_ind(f, indent + 1)
            }
            Case(case) => {
                writeln!(f, "{indent_str}match")?;
                case.value.format_ind(f, indent + 1)?;
                for (alternative, node) in &case.alternatives {
                    writeln!(
                        f,
                        "{indent_str}case {alternative}",
                        alternative = alternative
                    )?;
                    node.format_ind(f, indent + 1)?;
                }
                writeln!(f, "{indent_str}default")?;
                case.default.format_ind(f, indent + 1)
            }
        }
    }

    pub fn eval(&self, ctx: &mut EvalCtx) -> EvalResult {
        use Node::*;
        match self {
            Literal(value) => Ok(value.clone()),
            Apply(app) => {
                let function_value = app.function.eval(ctx)?;
                let function = function_value.as_function().unwrap().get();
                let function = function.borrow();
                let arguments = eval_args(&app.arguments, &function.ty.args, ctx)?;
                function.code.call(arguments, ctx)
            }
            StaticApply(app) => {
                let function = app.function.get();
                let function = function.borrow();
                let arguments = eval_args(&app.arguments, &function.ty.args, ctx)?;
                function.code.call(arguments, ctx)
            }
            EnvStore(node) => {
                let value = node.eval(ctx)?;
                ctx.environment.push(value.clone());
                Ok(value)
            }
            EnvLoad(index) => {
                let index = ctx.frame_base + *index;
                Ok(ctx.environment[index].clone())
            }
            BlockExpr(nodes) => {
                let env_size = ctx.environment.len();
                let return_value = nodes
                    .iter()
                    .try_fold(None, |_, node| Ok(Some(node.eval(ctx)?)))?
                    .unwrap_or(Value::unit());
                ctx.environment.truncate(env_size);
                Ok(return_value)
            }
            Assign(assignment) => {
                let value = assignment.value.eval(ctx)?;
                let target_ref = assignment.place.as_place(ctx)?.target_ref(ctx)?;
                *target_ref = value;
                Ok(Value::unit())
            }
            Tuple(nodes) => {
                let values = nodes.iter().try_fold(SVec2::new(), |mut nodes, node| {
                    nodes.push(node.eval(ctx)?);
                    Ok(nodes)
                })?;
                Ok(Value::Tuple(B::new(values)))
            }
            Project(node_and_index) => {
                let value = node_and_index.0.eval(ctx)?;
                Ok(match value {
                    Value::Tuple(tuple) => tuple.into_iter().nth(node_and_index.1).unwrap(),
                    Value::Variant(variant) => variant.value,
                    _ => panic!("Cannot project from a non-compound value"),
                })
            }
            Array(nodes) => {
                let values = eval_nodes(nodes, ctx)?;
                Ok(Value::native(array::Array::from_vec(values)))
            }
            Index(array, index) => {
                let index = index.eval(ctx)?.into_primitive_ty::<isize>().unwrap();
                let mut array = array
                    .eval(ctx)?
                    .into_primitive_ty::<array::Array>()
                    .unwrap();
                match array.get_mut_signed(index) {
                    Some(value) => Ok(value.clone()),
                    None => {
                        let len = array.len();
                        Err(RuntimeError::ArrayAccessOutOfBounds { index, len })
                    }
                }
            }
            Case(case) => {
                let value = case.value.eval(ctx)?;
                for (alternative, node) in &case.alternatives {
                    if value == *alternative {
                        return node.eval(ctx);
                    }
                }
                case.default.eval(ctx)
            }
        }
    }

    pub fn eval_and_print(&self, ctx: &mut EvalCtx) {
        match self.eval(ctx) {
            Ok(value) => println!("{value}"),
            Err(error) => println!("Runtime error: {error:?}"),
        }
    }

    pub fn as_place(&self, ctx: &mut EvalCtx) -> Result<Place, RuntimeError> {
        fn resolve_node(node: &Node, ctx: &mut EvalCtx) -> Result<Place, RuntimeError> {
            use Node::*;
            Ok(match node {
                Project(projection) => {
                    let (ref node, index) = **projection;
                    let mut place = resolve_node(node, ctx)?;
                    place.path.push(index as isize);
                    place
                }
                Index(array, index) => {
                    let mut place = resolve_node(array, ctx)?;
                    let index = index.eval(ctx)?.into_primitive_ty::<isize>().unwrap();
                    place.path.push(index);
                    place
                }
                EnvLoad(index) => Place {
                    // By using frame_base here, we allow to access parent frames
                    // when the ResolvedPlace is used in a child function.
                    target: ctx.frame_base + *index,
                    path: Vec::new(),
                },
                _ => panic!("Cannot resolve a non-place node"),
            })
        }
        resolve_node(self, ctx)
    }
}

impl std::fmt::Display for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.format_ind(f, 0)
    }
}

fn eval_nodes(nodes: &[Node], ctx: &mut EvalCtx) -> Result<Vec<Value>, RuntimeError> {
    eval_nodes_with(nodes.iter(), |node, ctx| node.eval(ctx), ctx)
}

fn eval_args(
    args: &[Node],
    args_ty: &[FnArgType],
    ctx: &mut EvalCtx,
) -> Result<Vec<ValOrMut>, RuntimeError> {
    let f = |(arg, ty): &(&Node, &FnArgType), ctx: &mut EvalCtx| {
        Ok(if ty.inout {
            ValOrMut::Mut(arg.as_place(ctx)?)
        } else {
            ValOrMut::Val(arg.eval(ctx)?)
        })
    };
    eval_nodes_with(args.iter().zip(args_ty), f, ctx)
}

fn eval_nodes_with<F, I, O, It>(
    mut inputs: It,
    f: F,
    ctx: &mut EvalCtx,
) -> Result<Vec<O>, RuntimeError>
where
    It: Iterator<Item = I>,
    F: Fn(&I, &mut EvalCtx) -> Result<O, RuntimeError>,
{
    inputs.try_fold(vec![], |mut output, input| {
        output.push(f(&input, ctx)?);
        Ok(output)
    })
}
