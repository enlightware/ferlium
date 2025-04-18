// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use ustr::Ustr;

use crate::{
    error::InternalCompilationError,
    internal_compilation_error,
    ir::{Node, NodeKind},
    r#type::FnArgType,
    Location,
};

enum PathPart {
    Projection(usize),
    FieldAccess(Ustr),
    IndexStatic(usize),
    IndexDynamic,
}

/// A path to a place in memory.
struct Path {
    variable: usize,
    parts: Vec<PathPart>,
}

impl Path {
    /// Builds a path for this node, assuming it is a place node, panicking otherwise.
    fn from_node(node: &Node) -> Self {
        use NodeKind::*;
        match &node.kind {
            Project(projection) => {
                let (ref node, index) = **projection;
                let mut path = Self::from_node(node);
                path.parts.push(PathPart::Projection(index));
                path
            }
            FieldAccess(access) => {
                let (ref node, field) = **access;
                let mut path = Self::from_node(node);
                path.parts.push(PathPart::FieldAccess(field));
                path
            }
            Index(array, index) => {
                let mut path = Self::from_node(array);
                if let NodeKind::Immediate(immediate) = &index.kind {
                    let index = *immediate.value.as_primitive_ty::<isize>().unwrap();
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
            EnvLoad(node) => Path {
                variable: node.index,
                parts: Vec::new(),
            },
            _ => panic!("Cannot resolve a non-place node"),
        }
    }
}

/// Returns whether the two nodes' path to memory are overlapping.
/// This assumes the nodes are path in the first place.
fn do_paths_overlap(a: &Path, b: &Path) -> bool {
    if a.variable != b.variable {
        return false;
    }
    for (a, b) in a.parts.iter().zip(b.parts.iter()) {
        use PathPart::*;
        match (a, b) {
            (Projection(a), Projection(b)) => {
                if a != b {
                    return false;
                }
            }
            (FieldAccess(a), FieldAccess(b)) => {
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

/// Implements borrow checking logic by comparing the paths of mutable arguments.
fn check_arguments(
    arg_types: &[FnArgType],
    arguments: &[Node],
    fn_span: Location,
) -> Result<(), InternalCompilationError> {
    // Collect all mutable arguments indices and their paths.
    let in_out_args: Vec<_> = arg_types
        .iter()
        .enumerate()
        .filter_map(|(i, ty)| {
            if ty.mut_ty.is_mutable() {
                Some((i, Path::from_node(&arguments[i])))
            } else {
                None
            }
        })
        .collect();
    // Compare all mutable arguments' paths pairwise.
    for (i, arg_i) in in_out_args.iter().enumerate() {
        for arg_j in in_out_args.iter().skip(i + 1) {
            if do_paths_overlap(&arg_i.1, &arg_j.1) {
                return Err(internal_compilation_error!(MutablePathsOverlap {
                    a_span: arguments[arg_i.0].span,
                    b_span: arguments[arg_j.0].span,
                    fn_span,
                }));
            }
        }
    }
    Ok(())
}

impl Node {
    pub fn check_borrows(&self) -> Result<(), InternalCompilationError> {
        use NodeKind::*;
        match &self.kind {
            Immediate(_) => (),
            BuildClosure(_) => panic!("Closure should not be in the IR at this point"),
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
            TraitFnApply(app) => {
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
            ProjectAt(_) => {
                panic!("ProjectAt should not be in the IR at this point");
            }
            Variant(variant) => {
                variant.1.check_borrows()?;
            }
            ExtractTag(node) => {
                node.check_borrows()?;
            }
            Record(nodes) => {
                for node in nodes.iter() {
                    node.check_borrows()?;
                }
            }
            FieldAccess(access) => {
                access.0.check_borrows()?;
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
            Loop(body) => {
                body.check_borrows()?;
            }
            SoftBreak => {}
        }
        Ok(())
    }
}
