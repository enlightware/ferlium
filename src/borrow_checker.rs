use lrpar::Span;

use crate::{
    error::InternalCompilationError,
    ir::{Node, NodeKind},
    r#type::FnArgType,
};

enum PathPart {
    Projection(usize),
    IndexStatic(usize),
    IndexDynamic,
}

struct Path {
    variable: usize,
    parts: Vec<PathPart>,
}

impl Path {
    fn from_node(node: &Node) -> Self {
        use NodeKind::*;
        match &node.kind {
            Project(projection) => {
                let (ref node, index) = **projection;
                let mut path = Self::from_node(node);
                path.parts.push(PathPart::Projection(index));
                path
            }
            Index(array, index) => {
                let mut path = Self::from_node(array);
                if let NodeKind::Literal(index) = &index.kind {
                    let index = *index.as_primitive_ty::<isize>().unwrap();
                    if index >= 0 {
                        path.parts.push(PathPart::IndexStatic(index as usize));
                    } else {
                        path.parts.push(PathPart::IndexDynamic);
                    }
                } else {
                    path.parts.push(PathPart::IndexDynamic);
                }
                path
            }
            EnvLoad(index) => Path {
                variable: *index,
                parts: Vec::new(),
            },
            _ => panic!("Cannot resolve a non-place node"),
        }
    }
}

/// Returns whether the two nodes' path to memory are overlapping.
/// This assumes the nodes are path in the first place.
fn do_paths_overlap(a: &Node, b: &Node) -> bool {
    let a = Path::from_node(a);
    let b = Path::from_node(b);
    if a.variable != b.variable {
        return false;
    }
    for (a, b) in a.parts.into_iter().zip(b.parts.into_iter()) {
        use PathPart::*;
        match (a, b) {
            (Projection(a), Projection(b)) => {
                if a != b {
                    return false;
                }
            }
            (IndexStatic(a), IndexStatic(b)) => {
                if a != b {
                    return false;
                }
            }
            _ => return true,
        }
    }
    true
}

/// Implement borrow checking logic by comparing the paths of mutable arguments.
fn check_arguments(
    arg_types: &[FnArgType],
    arguments: &[Node],
    fn_span: Span,
) -> Result<(), InternalCompilationError> {
    let in_out_indices: Vec<_> = arg_types
        .iter()
        .enumerate()
        .filter_map(|(i, ty)| if ty.inout.is_mutable() { Some(i) } else { None })
        .collect();
    for (i, arg_i) in in_out_indices.iter().enumerate() {
        for arg_j in in_out_indices.iter().skip(i + 1) {
            let arg_i = &arguments[*arg_i];
            let arg_j = &arguments[*arg_j];
            if do_paths_overlap(arg_i, arg_j) {
                return Err(InternalCompilationError::MutablePathsOverlap {
                    a_span: arg_i.span,
                    b_span: arg_j.span,
                    fn_span,
                });
            }
        }
    }
    Ok(())
}

impl Node {
    pub fn check_borrows(&self) -> Result<(), InternalCompilationError> {
        use NodeKind::*;
        match &self.kind {
            Literal(_) => (),
            Apply(app) => {
                app.function.check_borrows()?;
                for arg in &app.arguments {
                    arg.check_borrows()?;
                }
                let fn_type = app.function.ty.data();
                let fn_type = fn_type.as_function().unwrap();
                check_arguments(&fn_type.args, &app.arguments, app.function.span)?;
            }
            StaticApply(app) => {
                for arg in &app.arguments {
                    arg.check_borrows()?;
                }
                check_arguments(&app.ty.args, &app.arguments, app.function_span)?;
            }
            EnvStore(node) => {
                node.node.check_borrows()?;
            }
            EnvLoad(_) => {}
            Block(nodes) => {
                for node in nodes.iter() {
                    node.check_borrows()?;
                }
            }
            Assign(assignment) => {
                assignment.place.check_borrows()?;
                assignment.value.check_borrows()?;
            }
            Tuple(nodes) => {
                for node in nodes.iter() {
                    node.check_borrows()?;
                }
            }
            Project(projection) => {
                projection.0.check_borrows()?;
            }
            Array(nodes) => {
                for node in nodes.iter() {
                    node.check_borrows()?;
                }
            }
            Index(array, index) => {
                array.check_borrows()?;
                index.check_borrows()?;
            }
            Case(case) => {
                case.value.check_borrows()?;
                for (_, node) in case.alternatives.iter() {
                    node.check_borrows()?;
                }
                case.default.check_borrows()?;
            }
            Iterate(iteration) => {
                iteration.iterator.check_borrows()?;
                iteration.body.check_borrows()?;
            }
        }
        Ok(())
    }
}
