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
    compiler::error::{
        InternalCompilationError, InvalidSubscriptDefinitionKind, InvalidYieldKind,
        SubscriptDefinitionSubject,
    },
    hir::{CallArgument, Node, NodeArena, NodeId, NodeKind, function::ArgConvention},
    internal_compilation_error,
    module::{LocalDeclId, ULocalDecl, id::Id},
    types::r#type::Type,
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
            StaticApply(app) if app.ty.returns_place() => {
                Self::from_addressor_place_arguments(arena, &app.arguments)
            }
            FunctionApply(app) if app.ty.returns_place() => {
                Self::from_addressor_place_arguments(arena, &app.arguments)
            }
            TraitMethodApply(app) if app.ty.returns_place() => {
                Self::from_addressor_place_arguments(arena, &app.arguments)
            }
            CallDictionaryMethod(call) if call.ty.returns_place() => {
                Self::from_addressor_place_arguments(arena, &call.arguments)
            }
            SubscriptApply(app) if app.ty.returns_place() => {
                Self::from_addressor_place_arguments(arena, &app.arguments)
            }
            Block(block) => {
                let tail = block
                    .tail_node()
                    .expect("place block should have a tail expression");
                Self::from_node(arena, tail)
            }
            WithPlace(node) => Self::from_node(arena, node.place),
            LoadLocal(node) => Path {
                variable: node.id.as_index(),
                parts: Vec::new(),
            },
            _ => panic!("Cannot resolve a non-place node"),
        }
    }

    fn from_addressor_place_arguments(arena: &NodeArena, arguments: &[CallArgument]) -> Self {
        let base_index = arguments
            .iter()
            .position(|argument| !is_evidence_node(&arena[argument.value].kind))
            .expect("addressor-place application should have a base argument");
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
        NodeKind::GetDictionary(_)
            | NodeKind::LoadDictionary(_)
            | NodeKind::LoadSubscriptEvidence(_)
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

/// Return each immutable argument whose place overlaps an exclusive mutable argument.
///
/// The pair contains `(let_argument_index, mutable_argument_index)`. Multiple immutable
/// accesses may share a place; only immutable/mutable conflicts require a snapshot.
pub(crate) fn let_arguments_overlapping_mutable(
    arena: &NodeArena,
    arguments: &[CallArgument],
) -> Vec<(usize, usize)> {
    let mutable_paths = arguments
        .iter()
        .enumerate()
        .filter(|(_, argument)| argument.passing == ArgConvention::MutableRef)
        .map(|(index, argument)| (index, Path::from_node(arena, argument.value)))
        .collect::<Vec<_>>();

    arguments
        .iter()
        .enumerate()
        .filter(|(_, argument)| {
            argument.passing == ArgConvention::Let
                && crate::hir::node_is_place_reference(arena, argument.value)
                // A generic trait method is place-like for dictionary dispatch, but the
                // method value is metadata rather than aliasable source storage.
                && !matches!(arena[argument.value].kind, NodeKind::GetTraitMethod(_))
        })
        .flat_map(|(let_index, argument)| {
            let let_path = Path::from_node(arena, argument.value);
            mutable_paths
                .iter()
                .filter(move |(_, mutable_path)| do_paths_overlap(&let_path, mutable_path))
                .map(move |(mutable_index, _)| (let_index, *mutable_index))
        })
        .collect()
}

/// Implements borrow checking logic by comparing the paths of mutable arguments.
fn check_arguments(
    arguments: &[CallArgument],
    arena: &NodeArena,
    fn_span: Location,
) -> Result<(), InternalCompilationError> {
    // Collect all mutable arguments indices and their paths.
    let in_out_args: Vec<_> = arguments
        .iter()
        .enumerate()
        .filter_map(|(i, argument)| {
            if argument.passing == ArgConvention::MutableRef {
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

pub fn check_place_return_roots(
    arena: &NodeArena,
    node_id: NodeId,
    locals: &[ULocalDecl],
    base_parameter_index: Option<usize>,
    subject: SubscriptDefinitionSubject,
) -> Result<(), InternalCompilationError> {
    check_place_return_roots_in_node(arena, node_id, locals, base_parameter_index, subject)
}

pub fn check_yield_roots(
    arena: &NodeArena,
    node_id: NodeId,
    locals: &[ULocalDecl],
) -> Result<(), InternalCompilationError> {
    check_yield_roots_in_node(arena, node_id, locals)
}

fn check_yield_roots_in_node(
    arena: &NodeArena,
    node_id: NodeId,
    locals: &[ULocalDecl],
) -> Result<(), InternalCompilationError> {
    let node = &arena[node_id];
    if let NodeKind::Yield(value) = &node.kind {
        check_yield_root(arena, *value, locals)?;
    }
    for child in node.kind.child_node_ids() {
        check_yield_roots_in_node(arena, child, locals)?;
    }
    Ok(())
}

fn check_yield_root(
    arena: &NodeArena,
    node_id: NodeId,
    locals: &[ULocalDecl],
) -> Result<(), InternalCompilationError> {
    if arena[node_id].ty == Type::never() {
        return Ok(());
    }

    let Some(origin) = returned_place_origin(arena, node_id) else {
        return Err(internal_compilation_error!(InvalidYield {
            kind: InvalidYieldKind::NotAccessorOwned,
            span: arena[node_id].span,
        }));
    };

    match origin {
        PlaceOrigin::Direct {
            local: local_id, ..
        } if locals
            .get(local_id.as_index())
            .is_some_and(|local| local.may_own_storage()) =>
        {
            Ok(())
        }
        PlaceOrigin::Direct { .. } | PlaceOrigin::Addressor(_) => {
            Err(internal_compilation_error!(InvalidYield {
                kind: InvalidYieldKind::NotAccessorOwned,
                span: arena[node_id].span,
            }))
        }
    }
}

fn check_place_return_roots_in_node(
    arena: &NodeArena,
    node_id: NodeId,
    locals: &[ULocalDecl],
    base_parameter_index: Option<usize>,
    subject: SubscriptDefinitionSubject,
) -> Result<(), InternalCompilationError> {
    let node = &arena[node_id];
    if let NodeKind::Return(value) = &node.kind {
        check_place_return_root(arena, *value, locals, base_parameter_index, subject)?;
    }
    for child in node.kind.child_node_ids() {
        check_place_return_roots_in_node(arena, child, locals, base_parameter_index, subject)?;
    }
    Ok(())
}

fn check_place_return_root(
    arena: &NodeArena,
    node_id: NodeId,
    locals: &[ULocalDecl],
    base_parameter_index: Option<usize>,
    subject: SubscriptDefinitionSubject,
) -> Result<(), InternalCompilationError> {
    if arena[node_id].ty == Type::never() {
        return Ok(());
    }

    let Some(origin) = returned_place_origin(arena, node_id) else {
        return Err(internal_compilation_error!(InvalidSubscriptDefinition {
            subject,
            kind: InvalidSubscriptDefinitionKind::AddressorReturnMustBeCallerRooted,
            span: arena[node_id].span,
        }));
    };

    match origin {
        PlaceOrigin::Direct {
            local,
            through_projection,
        } if Some(local.as_index()) == base_parameter_index
            && (through_projection
                || locals
                    .get(local.as_index())
                    .is_some_and(|local| local.mut_ty.is_mutable())) =>
        {
            Ok(())
        }
        PlaceOrigin::Addressor(local_id) if Some(local_id.as_index()) == base_parameter_index => {
            Ok(())
        }
        PlaceOrigin::Direct { .. } | PlaceOrigin::Addressor(_) => {
            Err(internal_compilation_error!(InvalidSubscriptDefinition {
                subject,
                kind: InvalidSubscriptDefinitionKind::AddressorReturnMustBeRootedInBaseParameter,
                span: arena[node_id].span,
            }))
        }
    }
}

// Very conservative first addressor rule: a Ferlium addressor-place function can
// only return a place produced by another addressor call, and that call must be
// rooted in this function's base/receiver parameter: the first visible
// source-level parameter, after hidden closure captures if any. This is
// intentionally sound but limiting; later addressor forms should extend this
// provenance model rather than weaken the escape check.
#[derive(Clone, Copy)]
enum PlaceOrigin {
    /// A direct local place or projection rooted in a local.
    Direct {
        local: LocalDeclId,
        through_projection: bool,
    },
    /// A place produced by an addressor call whose base is rooted in a local.
    Addressor(LocalDeclId),
}

impl PlaceOrigin {
    fn local(self) -> LocalDeclId {
        match self {
            Self::Direct { local, .. } | Self::Addressor(local) => local,
        }
    }
}

fn returned_place_origin(arena: &NodeArena, node_id: NodeId) -> Option<PlaceOrigin> {
    let node = &arena[node_id];
    use NodeKind::*;
    match &node.kind {
        LoadLocal(load) => Some(PlaceOrigin::Direct {
            local: load.id,
            through_projection: false,
        }),
        Project(project) => {
            returned_place_origin(arena, project.value).map(|origin| PlaceOrigin::Direct {
                local: origin.local(),
                through_projection: true,
            })
        }
        FieldAccess(field_access) => {
            returned_place_origin(arena, field_access.value).map(|origin| PlaceOrigin::Direct {
                local: origin.local(),
                through_projection: true,
            })
        }
        StaticApply(app) if app.ty.returns_place() => addressor_base_origin(arena, &app.arguments),
        FunctionApply(app) if app.ty.returns_place() => {
            addressor_base_origin(arena, &app.arguments)
        }
        TraitMethodApply(app) if app.ty.returns_place() => {
            addressor_base_origin(arena, &app.arguments)
        }
        CallDictionaryMethod(call) if call.ty.returns_place() => {
            addressor_base_origin(arena, &call.arguments)
        }
        SubscriptApply(app) if app.ty.returns_place() => {
            addressor_base_origin(arena, &app.arguments)
        }
        WithPlace(node) => returned_place_origin(arena, node.place),
        Block(block) => block
            .body
            .last()
            .and_then(|tail| returned_place_origin(arena, *tail)),
        _ => None,
    }
}

fn addressor_base_origin(arena: &NodeArena, arguments: &[CallArgument]) -> Option<PlaceOrigin> {
    let base_index = arguments
        .iter()
        .position(|argument| !is_evidence_node(&arena[argument.value].kind))?;
    returned_place_origin(arena, arguments[base_index].value)
        .map(|origin| PlaceOrigin::Addressor(origin.local()))
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
            BuildSubscriptValue(build) => {
                check_borrows(arena, build.subscript)?;
                for &capture in &build.evidence_captures {
                    check_borrows(arena, capture)?;
                }
            }
            FunctionApply(app) => {
                check_borrows(arena, app.function)?;
                for arg in &app.arguments {
                    check_borrows(arena, arg.value)?;
                }
                check_arguments(&app.arguments, arena, arena[app.function].span)?;
            }
            SubscriptApply(app) => {
                check_borrows(arena, app.subscript)?;
                for arg in &app.arguments {
                    check_borrows(arena, arg.value)?;
                }
                check_arguments(&app.arguments, arena, self.span)?;
            }
            CloneClosureEnv(node) => {
                check_borrows(arena, node.source)?;
            }
            DropClosureEnv(node) => {
                check_borrows(arena, node.target)?;
            }
            CloneSubscriptValue(node) => {
                check_borrows(arena, node.source)?;
            }
            DropSubscriptValue(node) => {
                check_borrows(arena, node.target)?;
            }
            CloneValue(node) => {
                check_borrows(arena, node.source)?;
            }
            StaticApply(app) => {
                for arg in &app.arguments {
                    check_borrows(arena, arg.value)?;
                }
                check_arguments(&app.arguments, arena, app.function_span)?;
            }
            TraitMethodApply(app) => {
                for arg in &app.arguments {
                    check_borrows(arena, arg.value)?;
                }
                check_arguments(&app.arguments, arena, app.method_span)?;
            }
            GetFunction(_) | GetSubscript(_) => {}
            GetTraitMethod(_) | GetTraitAssociatedConst(_) | GetTraitDictionary(_) => {}
            GetDictionary(_) => {}
            LoadDictionary(_) | LoadSubscriptEvidence(_) => {}
            GetDictionaryMethod(node) => check_borrows(arena, node.dictionary)?,
            GetDictionaryAssociatedConst(node) => check_borrows(arena, node.dictionary)?,
            CallDictionaryMethod(node) => {
                check_borrows(arena, node.dictionary)?;
                for arg in &node.arguments {
                    check_borrows(arena, arg.value)?;
                }
                check_arguments(&node.arguments, arena, arena[node.dictionary].span)?;
            }
            StoreLocal(node) => {
                check_borrows(arena, node.value)?;
            }
            TakeLocalValue(_) => {}
            LoadLocal(_) => {}
            Return(node_id) => {
                check_borrows(arena, *node_id)?;
            }
            Yield(node_id) => {
                check_borrows(arena, *node_id)?;
            }
            WithYielded(node) => {
                check_borrows(arena, node.accessor)?;
                check_borrows(arena, node.body)?;
            }
            WithPlace(node) => {
                check_borrows(arena, node.place)?;
                check_borrows(arena, node.body)?;
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
            Loop(node) => {
                check_borrows(arena, node.body)?;
            }
            Break(node) => {
                check_borrows(arena, node.value)?;
            }
            CheckCallDepth | CheckFuel | Continue(_) => {}
        }
        Ok(())
    }
}
