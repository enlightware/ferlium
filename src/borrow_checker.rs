// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use ustr::Ustr;

use crate::{
    Location,
    error::InternalCompilationError,
    internal_compilation_error,
    ir::{Node, NodeArena, NodeId, NodeKind},
    r#type::FnArgType,
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
    fn from_node(arena: &NodeArena, id: NodeId) -> Self {
        let node = &arena[id];
        use NodeKind::*;
        match &node.kind {
            Project(data, index) => {
                let mut path = Self::from_node(arena, *data);
                path.parts.push(PathPart::Projection(*index));
                path
            }
            FieldAccess(data, field) => {
                let mut path = Self::from_node(arena, *data);
                path.parts.push(PathPart::FieldAccess(*field));
                path
            }
            Index(array, index) => {
                let mut path = Self::from_node(arena, *array);
                if let NodeKind::Immediate(immediate) = &arena[*index].kind {
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
                variable: node.index as usize,
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
    arguments: &[NodeId],
    arena: &NodeArena,
    fn_span: Location,
) -> Result<(), InternalCompilationError> {
    // Collect all mutable arguments indices and their paths.
    let in_out_args: Vec<_> = arg_types
        .iter()
        .enumerate()
        .filter_map(|(i, ty)| {
            if ty.mut_ty.is_mutable() {
                Some((i, Path::from_node(arena, arguments[i])))
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
                    a_span: arena[arguments[arg_i.0]].span,
                    b_span: arena[arguments[arg_j.0]].span,
                    fn_span,
                }));
            }
        }
    }
    Ok(())
}

pub fn check_borrows(arena: &NodeArena, id: NodeId) -> Result<(), InternalCompilationError> {
    arena[id].check_borrows(arena)
}

impl Node {
    pub fn check_borrows(&self, arena: &NodeArena) -> Result<(), InternalCompilationError> {
        use NodeKind::*;
        match &self.kind {
            Immediate(_) => {}
            BuildClosure(build_closure) => {
                check_borrows(arena, build_closure.function)?;
                for &capture in &build_closure.captures {
                    check_borrows(arena, capture)?;
                }
            }
            Apply(app) => {
                check_borrows(arena, app.function)?;
                for &arg in &app.arguments {
                    check_borrows(arena, arg)?;
                }
                let fn_type = arena[app.function].ty.data();
                let fn_type = fn_type.as_function().unwrap();
                check_arguments(
                    &fn_type.args,
                    &app.arguments,
                    arena,
                    arena[app.function].span,
                )?;
            }
            StaticApply(app) => {
                for &arg in &app.arguments {
                    check_borrows(arena, arg)?;
                }
                check_arguments(&app.ty.args, &app.arguments, arena, app.function_span)?;
            }
            TraitFnApply(app) => {
                for &arg in &app.arguments {
                    check_borrows(arena, arg)?;
                }
                check_arguments(&app.ty.args, &app.arguments, arena, app.function_span)?;
            }
            GetFunction(_) => {}
            GetDictionary(_) => {}
            EnvStore(node) => {
                check_borrows(arena, node.value)?;
            }
            EnvLoad(_) => {}
            Return(node_id) => {
                check_borrows(arena, *node_id)?;
            }
            Block(nodes) => {
                for &node_id in nodes.iter() {
                    check_borrows(arena, node_id)?;
                }
            }
            Assign(assignment) => {
                check_borrows(arena, assignment.place)?;
                check_borrows(arena, assignment.value)?;
            }
            Tuple(nodes) => {
                for &node_id in nodes.iter() {
                    check_borrows(arena, node_id)?;
                }
            }
            Project(data, _) => {
                check_borrows(arena, *data)?;
            }
            ProjectAt(_, _) => {
                panic!("ProjectAt should not be in the IR at this point");
            }
            Variant(_, payload) => {
                check_borrows(arena, *payload)?;
            }
            ExtractTag(node_id) => {
                check_borrows(arena, *node_id)?;
            }
            Record(nodes) => {
                for &node_id in nodes.iter() {
                    check_borrows(arena, node_id)?;
                }
            }
            FieldAccess(data, _) => {
                check_borrows(arena, *data)?;
            }
            Array(nodes) => {
                for &node_id in nodes.iter() {
                    check_borrows(arena, node_id)?;
                }
            }
            Index(array, index) => {
                check_borrows(arena, *array)?;
                check_borrows(arena, *index)?;
            }
            Case(case) => {
                check_borrows(arena, case.value)?;
                for &(_, node_id) in case.alternatives.iter() {
                    check_borrows(arena, node_id)?;
                }
                check_borrows(arena, case.default)?;
            }
            Loop(body) => {
                check_borrows(arena, *body)?;
            }
            SoftBreak | Unimplemented => {}
        }
        Ok(())
    }
}
