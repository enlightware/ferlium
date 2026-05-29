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
    compiler::error::InternalCompilationError,
    hir::{CallArgument, Node, NodeArena, NodeId, NodeKind},
    internal_compilation_error,
    module::id::Id,
    types::r#type::FnArgType,
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
    fn from_node(arena: &NodeArena, node_id: NodeId) -> Self {
        let node = &arena[node_id];
        use NodeKind::*;
        match &node.kind {
            Project(project) => {
                let mut path = Self::from_node(arena, project.value);
                path.parts
                    .push(PathPart::Projection(project.index.as_index()));
                path
            }
            FieldAccess(field_access) => {
                let mut path = Self::from_node(arena, field_access.value);
                path.parts.push(PathPart::FieldAccess(field_access.field));
                path
            }
            StaticApply(app) if app.returns_place => {
                Self::from_place_result_arguments(arena, &app.arguments)
            }
            Apply(app) if app.returns_place => {
                Self::from_place_result_arguments(arena, &app.arguments)
            }
            LoadLocal(node) => Path {
                variable: node.id.as_index(),
                parts: Vec::new(),
            },
            _ => panic!("Cannot resolve a non-place node"),
        }
    }

    fn from_place_result_arguments(arena: &NodeArena, arguments: &[CallArgument]) -> Self {
        let base_index = arguments
            .iter()
            .position(|argument| !is_evidence_node(&arena[argument.value].kind))
            .expect("place_result application should have a base argument");
        let mut path = Self::from_node(arena, arguments[base_index].value);
        if let Some(index) = arguments.get(base_index + 1) {
            path.parts.push(Self::index_part(arena, index.value));
        } else {
            path.parts.push(PathPart::IndexDynamic);
        }
        path
    }

    fn index_part(arena: &NodeArena, node_id: NodeId) -> PathPart {
        if let NodeKind::Immediate(immediate) = &arena[node_id].kind {
            let index = *immediate.as_primitive_ty::<isize>().unwrap();
            if index >= 0 {
                return PathPart::IndexStatic(index as usize);
            }
        }
        PathPart::IndexDynamic
    }
}

fn is_evidence_node(kind: &NodeKind) -> bool {
    matches!(
        kind,
        NodeKind::GetDictionary(_) | NodeKind::LoadDictionary(_) | NodeKind::LoadFieldIndex(_)
    )
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
    arguments: &[CallArgument],
    arena: &NodeArena,
    fn_span: Location,
) -> Result<(), InternalCompilationError> {
    // Collect all mutable arguments indices and their paths.
    let in_out_args: Vec<_> = arg_types
        .iter()
        .enumerate()
        .filter_map(|(i, ty)| {
            if ty.mut_ty.is_mutable() {
                Some((i, Path::from_node(arena, arguments[i].value)))
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
                    a_span: arena[arguments[arg_i.0].value].span,
                    b_span: arena[arguments[arg_j.0].value].span,
                    fn_span,
                }));
            }
        }
    }
    Ok(())
}

pub fn check_borrows(arena: &NodeArena, node_id: NodeId) -> Result<(), InternalCompilationError> {
    arena[node_id].check_borrows(arena)
}

impl Node {
    pub fn check_borrows(&self, arena: &NodeArena) -> Result<(), InternalCompilationError> {
        use NodeKind::*;
        match &self.kind {
            Immediate(_) | Uninit => {}
            BuildClosure(build_closure) => {
                check_borrows(arena, build_closure.function)?;
                for &capture in &build_closure.dictionary_captures {
                    check_borrows(arena, capture)?;
                }
                for &capture in &build_closure.captures {
                    check_borrows(arena, capture)?;
                }
                if let Some(dict) = build_closure.captures_value_dictionary {
                    check_borrows(arena, dict)?;
                }
            }
            Apply(app) => {
                check_borrows(arena, app.function)?;
                for arg in &app.arguments {
                    check_borrows(arena, arg.value)?;
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
            CloneClosureEnv(node) => {
                check_borrows(arena, node.source)?;
                check_borrows(arena, node.target)?;
            }
            DropClosureEnv(node) => {
                check_borrows(arena, node.target)?;
            }
            CloneValue(node) => {
                check_borrows(arena, node.source)?;
            }
            StaticApply(app) => {
                for arg in &app.arguments {
                    check_borrows(arena, arg.value)?;
                }
                check_arguments(&app.ty.args, &app.arguments, arena, app.function_span)?;
            }
            TraitMethodApply(app) => {
                for arg in &app.arguments {
                    check_borrows(arena, arg.value)?;
                }
                check_arguments(&app.ty.args, &app.arguments, arena, app.method_span)?;
            }
            GetFunction(_) => {}
            GetTraitMethod(_) => {}
            GetTraitAssociatedConst(_) => {}
            GetTraitDictionary(_) => {}
            GetDictionary(_) => {}
            LoadDictionary(_) | LoadFieldIndex(_) => {}
            GetDictionaryMethod(node) => check_borrows(arena, node.dictionary)?,
            GetDictionaryAssociatedConst(node) => check_borrows(arena, node.dictionary)?,
            CallDictionaryMethod(node) => {
                check_borrows(arena, node.dictionary)?;
                for arg in &node.arguments {
                    check_borrows(arena, arg.value)?;
                }
                check_arguments(
                    &node.ty.args,
                    &node.arguments,
                    arena,
                    arena[node.dictionary].span,
                )?;
            }
            StoreLocal(node) => {
                check_borrows(arena, node.value)?;
            }
            TakeLocalValue(_) => {}
            LoadLocal(_) => {}
            Return(node_id) => {
                check_borrows(arena, *node_id)?;
            }
            Block(block) => {
                for &node_id in block.body.iter() {
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
            Project(project) => {
                check_borrows(arena, project.value)?;
            }
            ProjectAt(_) => {
                panic!("ProjectAt should not be in the HIR at this point");
            }
            Variant(variant) => {
                check_borrows(arena, variant.payload)?;
            }
            ExtractTag(node_id) => {
                check_borrows(arena, *node_id)?;
            }
            Record(nodes) => {
                for &node_id in nodes.iter() {
                    check_borrows(arena, node_id)?;
                }
            }
            FieldAccess(field_access) => {
                check_borrows(arena, field_access.value)?;
            }
            Array(nodes) => {
                for &node_id in nodes.iter() {
                    check_borrows(arena, node_id)?;
                }
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
            CheckCallDepth | CheckFuel | SoftBreak | Unimplemented => {}
        }
        Ok(())
    }
}
