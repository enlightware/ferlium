// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use smallvec::smallvec;
use ustr::Ustr;

use crate::{
    Location,
    compiler::error::{
        InternalCompilationError, InvalidSubscriptDefinitionKind, InvalidYieldKind,
        SubscriptDefinitionSubject,
    },
    containers::SVec4,
    hir::{
        CallArgument, ENodeArena, ENodeId, Elaborated, NodeArena, NodeId, NodeKind,
        function::ArgConvention, node_is_place_reference,
    },
    internal_compilation_error,
    module::{ELocalDecl, LocalDeclId, id::Id},
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
    fn from_local(id: LocalDeclId) -> Self {
        Self {
            variable: id.as_index(),
            parts: Vec::new(),
        }
    }

    /// Builds a path for this node, assuming it is a place node, panicking otherwise.
    fn from_node(arena: &NodeArena, node_id: NodeId) -> Self {
        Self::try_from_node(arena, node_id).expect("Cannot resolve a non-place node")
    }

    /// Builds a caller-storage path when `node_id` is rooted in an existing local.
    ///
    /// Some projection nodes are place-shaped but rooted in a temporary value. They cannot alias
    /// an earlier caller place and are deliberately rejected by this fallible form. The ordered
    /// argument analysis runs before temporary-place normalization, unlike the established borrow
    /// checks that use [`Self::from_node`].
    fn try_from_node(arena: &NodeArena, node_id: NodeId) -> Option<Self> {
        let node = &arena[node_id];
        use NodeKind::*;
        match &node.kind {
            Project(project) => {
                let mut path = Self::try_from_node(arena, project.value)?;
                path.parts
                    .push(PathPart::Projection(project.index.as_index()));
                Some(path)
            }
            FieldAccess(field_access) => {
                let mut path = Self::try_from_node(arena, field_access.value)?;
                path.parts.push(PathPart::FieldAccess(field_access.field));
                Some(path)
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
                Self::try_from_node(arena, tail)
            }
            WithPlace(node) => Self::try_from_node(arena, node.place),
            LoadLocal(node) => Some(Self::from_local(node.id)),
            _ => None,
        }
    }

    fn from_addressor_place_arguments(
        arena: &NodeArena,
        arguments: &[CallArgument],
    ) -> Option<Self> {
        let base_index = arguments
            .iter()
            .position(|argument| !is_evidence_node(&arena[argument.value].kind))
            .expect("addressor-place application should have a base argument");
        let mut path = Self::try_from_node(arena, arguments[base_index].value)?;
        if let Some(index) = arguments.get(base_index + 1) {
            path.parts.push(Self::index_part(arena, index.value));
        } else {
            path.parts.push(PathPart::IndexDynamic);
        }
        Some(path)
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

fn call_arguments(kind: &NodeKind) -> Option<&[CallArgument]> {
    match kind {
        NodeKind::FunctionApply(app) => Some(&app.arguments),
        NodeKind::SubscriptApply(app) => Some(&app.arguments),
        NodeKind::StaticApply(app) => Some(&app.arguments),
        NodeKind::TraitMethodApply(app) => Some(&app.arguments),
        NodeKind::CallDictionaryMethod(call) => Some(&call.arguments),
        _ => None,
    }
}

/// Whether evaluating `node_id` may write a place overlapping `observed`.
///
/// Calls can only mutate caller storage through `MutableRef` arguments. Direct assignments and
/// ownership operations name their destination storage in HIR. Walking those operations gives
/// call-lifetime planning the local write footprint that ordinary effect types intentionally do
/// not carry. Keep this query on unelaborated HIR: both type inference and final HIR elaboration
/// need to make the same semantic snapshot decision from the original argument expressions.
fn evaluation_may_write_path(arena: &NodeArena, node_id: NodeId, observed: &Path) -> bool {
    let node = &arena[node_id];

    match &node.kind {
        NodeKind::Assign(assign) => {
            if node_is_place_reference(arena, assign.place) {
                match Path::try_from_node(arena, assign.place) {
                    Some(written) if do_paths_overlap(&written, observed) => return true,
                    // A place-shaped destination without a caller-storage path is rooted in a
                    // temporary and cannot alias `observed`.
                    Some(_) | None => {}
                }
            }
        }
        NodeKind::StoreLocal(store) => {
            if do_paths_overlap(&Path::from_local(store.id), observed) {
                return true;
            }
        }
        NodeKind::TakeLocalValue(take) => {
            if do_paths_overlap(&Path::from_local(take.id), observed) {
                return true;
            }
        }
        NodeKind::DropClosureEnv(drop) if node_is_place_reference(arena, drop.target) => {
            match Path::try_from_node(arena, drop.target) {
                Some(written) if do_paths_overlap(&written, observed) => return true,
                Some(_) | None => {}
            }
        }
        NodeKind::DropSubscriptValue(drop) if node_is_place_reference(arena, drop.target) => {
            match Path::try_from_node(arena, drop.target) {
                Some(written) if do_paths_overlap(&written, observed) => return true,
                Some(_) | None => {}
            }
        }
        _ => {}
    }

    if call_arguments(&node.kind).is_some_and(|arguments| {
        arguments.iter().any(|argument| {
            argument.passing == ArgConvention::MutableRef
                && Path::try_from_node(arena, argument.value)
                    .is_some_and(|written| do_paths_overlap(&written, observed))
        })
    }) {
        return true;
    }

    node.kind
        .child_node_ids()
        .into_iter()
        .any(|child| evaluation_may_write_path(arena, child, observed))
}

/// Return each `Let` place whose observed value may be changed while a later argument is
/// evaluated.
///
/// The pair contains `(let_argument_index, writing_argument_index)`. This is distinct from the
/// simultaneous `Let`/`MutableRef` conflict checked below: the write happens before the outer call,
/// but after the earlier argument's source-level evaluation point. The earlier value therefore
/// needs a snapshot at that point.
pub(crate) fn let_arguments_overlapping_later_argument_writes(
    arena: &NodeArena,
    arguments: &[CallArgument],
) -> Vec<(usize, usize)> {
    arguments
        .iter()
        .enumerate()
        .filter(|(_, argument)| {
            argument.passing == ArgConvention::Let
                && crate::hir::node_is_place_reference(arena, argument.value)
                && !matches!(arena[argument.value].kind, NodeKind::GetTraitMethod(_))
        })
        .filter_map(|(let_index, argument)| {
            Path::try_from_node(arena, argument.value).map(|observed| (let_index, observed))
        })
        .flat_map(|(let_index, observed)| {
            arguments
                .iter()
                .enumerate()
                .skip(let_index + 1)
                .filter(move |(_, later)| evaluation_may_write_path(arena, later.value, &observed))
                .map(move |(writing_index, _)| (let_index, writing_index))
        })
        .collect()
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

/// A compact provenance summary used to ensure that a returned or yielded place cannot outlive
/// its storage.
///
/// It records the local at the root of the place and whether the place is produced directly or by
/// an addressor call. Addressor-place returns must remain rooted in the function's base/receiver
/// parameter (the first visible source parameter after hidden captures), while yielded places must
/// refer directly to storage owned by the suspended accessor. The summary is intentionally
/// conservative; supporting additional place-producing forms should extend the provenance it
/// records without weakening these escape checks.
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

impl Path {
    fn from_enode(arena: &ENodeArena, node_id: ENodeId) -> Self {
        Self::try_from_enode(arena, node_id).expect("Cannot resolve a non-place node")
    }

    fn try_from_enode(arena: &ENodeArena, node_id: ENodeId) -> Option<Self> {
        let node = &arena[node_id];
        use NodeKind::*;
        match &node.kind {
            Project(project) => {
                let mut path = Self::try_from_enode(arena, project.value)?;
                path.parts
                    .push(PathPart::Projection(project.index.as_index()));
                Some(path)
            }
            StaticApply(app) if app.ty.returns_place() => {
                Self::from_enode_addressor_arguments(arena, &app.arguments)
            }
            FunctionApply(app) if app.ty.returns_place() => {
                Self::from_enode_addressor_arguments(arena, &app.arguments)
            }
            CallDictionaryMethod(call) if call.ty.returns_place() => {
                Self::from_enode_addressor_arguments(arena, &call.arguments)
            }
            SubscriptApply(app) if app.ty.returns_place() => {
                Self::from_enode_addressor_arguments(arena, &app.arguments)
            }
            Block(block) => block
                .tail_node()
                .and_then(|tail| Self::try_from_enode(arena, tail)),
            WithPlace(node) => Self::try_from_enode(arena, node.place),
            LoadLocal(node) => Some(Self::from_local(node.id)),
            FieldAccess(never)
            | TraitMethodApply(never)
            | GetTraitMethod(never)
            | GetTraitAssociatedConst(never)
            | GetTraitDictionary(never) => match *never {},
            _ => None,
        }
    }

    fn from_enode_addressor_arguments(
        arena: &ENodeArena,
        arguments: &[CallArgument<Elaborated>],
    ) -> Option<Self> {
        let base_index = arguments
            .iter()
            .position(|argument| !is_enode_evidence(&arena[argument.value].kind))
            .expect("addressor-place application should have a base argument");
        let mut path = Self::try_from_enode(arena, arguments[base_index].value)?;
        if let Some(index) = arguments.get(base_index + 1) {
            path.parts.push(Self::enode_index_part(arena, index.value));
        } else {
            path.parts.push(PathPart::IndexDynamic);
        }
        Some(path)
    }

    fn enode_index_part(arena: &ENodeArena, node_id: ENodeId) -> PathPart {
        if let NodeKind::Immediate(immediate) = &arena[node_id].kind {
            let index = *immediate.as_primitive_ty::<isize>().unwrap();
            if index >= 0 {
                return PathPart::IndexStatic(index as usize);
            }
        }
        PathPart::IndexDynamic
    }
}

fn is_enode_evidence(kind: &NodeKind<Elaborated>) -> bool {
    matches!(
        kind,
        NodeKind::GetDictionary(_)
            | NodeKind::LoadDictionary(_)
            | NodeKind::LoadSubscriptEvidence(_)
    )
}

fn check_elaborated_arguments(
    arguments: &[CallArgument<Elaborated>],
    arena: &ENodeArena,
    fn_span: Location,
) -> Result<(), InternalCompilationError> {
    let mutable_paths = arguments
        .iter()
        .enumerate()
        .filter(|(_, argument)| argument.passing == ArgConvention::MutableRef)
        .map(|(index, argument)| (index, Path::from_enode(arena, argument.value)))
        .collect::<Vec<_>>();
    for (index, left) in mutable_paths.iter().enumerate() {
        for right in mutable_paths.iter().skip(index + 1) {
            if do_paths_overlap(&left.1, &right.1) {
                return Err(internal_compilation_error!(MutablePathsOverlap {
                    a_span: arena[arguments[left.0].value].span,
                    b_span: arena[arguments[right.0].value].span,
                    fn_span,
                }));
            }
        }
    }
    Ok(())
}

pub fn check_elaborated_borrows(
    arena: &ENodeArena,
    node_id: ENodeId,
) -> Result<(), InternalCompilationError> {
    let node = &arena[node_id];
    match &node.kind {
        NodeKind::FunctionApply(app) => {
            check_elaborated_arguments(&app.arguments, arena, arena[app.function].span)?;
        }
        NodeKind::SubscriptApply(app) => {
            check_elaborated_arguments(&app.arguments, arena, node.span)?;
        }
        NodeKind::StaticApply(app) => {
            check_elaborated_arguments(&app.arguments, arena, app.function_span)?;
        }
        NodeKind::CallDictionaryMethod(call) => {
            check_elaborated_arguments(&call.arguments, arena, arena[call.dictionary].span)?;
        }
        _ => {}
    }
    for child in elaborated_child_node_ids(&node.kind) {
        check_elaborated_borrows(arena, child)?;
    }
    Ok(())
}

pub fn check_elaborated_yield_roots(
    arena: &ENodeArena,
    node_id: ENodeId,
    locals: &[ELocalDecl],
) -> Result<(), InternalCompilationError> {
    check_elaborated_yield_roots_in_node(arena, node_id, locals)
}

fn check_elaborated_yield_roots_in_node(
    arena: &ENodeArena,
    node_id: ENodeId,
    locals: &[ELocalDecl],
) -> Result<(), InternalCompilationError> {
    let node = &arena[node_id];
    if let NodeKind::Yield(value) = &node.kind {
        check_elaborated_yield_root(arena, *value, locals)?;
    }
    for child in elaborated_child_node_ids(&node.kind) {
        check_elaborated_yield_roots_in_node(arena, child, locals)?;
    }
    Ok(())
}

fn check_elaborated_yield_root(
    arena: &ENodeArena,
    node_id: ENodeId,
    locals: &[ELocalDecl],
) -> Result<(), InternalCompilationError> {
    if arena[node_id].ty == Type::never() {
        return Ok(());
    }
    let valid =
        elaborated_returned_place_origin(arena, node_id).is_some_and(|origin| match origin {
            PlaceOrigin::Direct { local, .. } => locals
                .get(local.as_index())
                .is_some_and(|local| local.owns_storage()),
            PlaceOrigin::Addressor(_) => false,
        });
    if valid {
        Ok(())
    } else {
        Err(internal_compilation_error!(InvalidYield {
            kind: InvalidYieldKind::NotAccessorOwned,
            span: arena[node_id].span,
        }))
    }
}

pub fn check_elaborated_place_return_roots(
    arena: &ENodeArena,
    node_id: ENodeId,
    locals: &[ELocalDecl],
    base_parameter_index: Option<usize>,
    subject: SubscriptDefinitionSubject,
) -> Result<(), InternalCompilationError> {
    let node = &arena[node_id];
    if let NodeKind::Return(value) = &node.kind {
        check_elaborated_place_return_root(arena, *value, locals, base_parameter_index, subject)?;
    }
    for child in elaborated_child_node_ids(&node.kind) {
        check_elaborated_place_return_roots(arena, child, locals, base_parameter_index, subject)?;
    }
    Ok(())
}

fn check_elaborated_place_return_root(
    arena: &ENodeArena,
    node_id: ENodeId,
    locals: &[ELocalDecl],
    base_parameter_index: Option<usize>,
    subject: SubscriptDefinitionSubject,
) -> Result<(), InternalCompilationError> {
    if arena[node_id].ty == Type::never() {
        return Ok(());
    }
    let Some(origin) = elaborated_returned_place_origin(arena, node_id) else {
        return Err(internal_compilation_error!(InvalidSubscriptDefinition {
            subject,
            kind: InvalidSubscriptDefinitionKind::AddressorReturnMustBeCallerRooted,
            span: arena[node_id].span,
        }));
    };
    let valid = match origin {
        PlaceOrigin::Direct {
            local,
            through_projection,
        } => {
            Some(local.as_index()) == base_parameter_index
                && (through_projection
                    || locals
                        .get(local.as_index())
                        .is_some_and(|local| local.mut_ty.is_mutable()))
        }
        PlaceOrigin::Addressor(local) => Some(local.as_index()) == base_parameter_index,
    };
    if valid {
        Ok(())
    } else {
        Err(internal_compilation_error!(InvalidSubscriptDefinition {
            subject,
            kind: InvalidSubscriptDefinitionKind::AddressorReturnMustBeRootedInBaseParameter,
            span: arena[node_id].span,
        }))
    }
}

fn elaborated_returned_place_origin(arena: &ENodeArena, node_id: ENodeId) -> Option<PlaceOrigin> {
    use NodeKind::*;
    match &arena[node_id].kind {
        LoadLocal(load) => Some(PlaceOrigin::Direct {
            local: load.id,
            through_projection: false,
        }),
        Project(project) => elaborated_returned_place_origin(arena, project.value).map(|origin| {
            PlaceOrigin::Direct {
                local: origin.local(),
                through_projection: true,
            }
        }),
        StaticApply(app) if app.ty.returns_place() => {
            elaborated_addressor_base_origin(arena, &app.arguments)
        }
        FunctionApply(app) if app.ty.returns_place() => {
            elaborated_addressor_base_origin(arena, &app.arguments)
        }
        CallDictionaryMethod(call) if call.ty.returns_place() => {
            elaborated_addressor_base_origin(arena, &call.arguments)
        }
        SubscriptApply(app) if app.ty.returns_place() => {
            elaborated_addressor_base_origin(arena, &app.arguments)
        }
        WithPlace(with) => elaborated_returned_place_origin(arena, with.place),
        Block(block) => block
            .tail_node()
            .and_then(|tail| elaborated_returned_place_origin(arena, tail)),
        FieldAccess(never)
        | TraitMethodApply(never)
        | GetTraitMethod(never)
        | GetTraitAssociatedConst(never)
        | GetTraitDictionary(never) => match *never {},
        _ => None,
    }
}

fn elaborated_addressor_base_origin(
    arena: &ENodeArena,
    arguments: &[CallArgument<Elaborated>],
) -> Option<PlaceOrigin> {
    let base_index = arguments
        .iter()
        .position(|argument| !is_enode_evidence(&arena[argument.value].kind))?;
    elaborated_returned_place_origin(arena, arguments[base_index].value)
        .map(|origin| PlaceOrigin::Addressor(origin.local()))
}

fn elaborated_child_node_ids(kind: &NodeKind<Elaborated>) -> SVec4<ENodeId> {
    use NodeKind::*;
    match kind {
        Immediate(_)
        | Uninit
        | GetFunction(_)
        | GetSubscript(_)
        | GetDictionary(_)
        | LoadDictionary(_)
        | LoadSubscriptEvidence(_)
        | TakeLocalValue(_)
        | LoadLocal(_)
        | CheckCallDepth
        | CheckFuel
        | Continue(_) => smallvec![],
        BuildClosure(build) => std::iter::once(build.function)
            .chain(build.dictionary_captures.iter().copied())
            .chain(build.captures.iter().copied())
            .chain(build.captures_value_dictionary)
            .collect(),
        BuildSubscriptValue(build) => std::iter::once(build.subscript)
            .chain(build.evidence_captures.iter().copied())
            .collect(),
        FunctionApply(app) => std::iter::once(app.function)
            .chain(app.arguments.iter().map(|argument| argument.value))
            .collect(),
        SubscriptApply(app) => std::iter::once(app.subscript)
            .chain(app.arguments.iter().map(|argument| argument.value))
            .collect(),
        StaticApply(app) => app
            .extra_arguments
            .iter()
            .copied()
            .chain(app.arguments.iter().map(|argument| argument.value))
            .collect(),
        CallDictionaryMethod(call) => std::iter::once(call.dictionary)
            .chain(call.arguments.iter().map(|argument| argument.value))
            .collect(),
        CloneClosureEnv(operation) => smallvec![operation.source],
        DropClosureEnv(operation) => smallvec![operation.target],
        CloneSubscriptValue(operation) => smallvec![operation.source],
        DropSubscriptValue(operation) => smallvec![operation.target],
        CloneValue(operation) => smallvec![operation.source],
        GetDictionaryMethod(operation) => smallvec![operation.dictionary],
        GetDictionaryAssociatedConst(operation) => smallvec![operation.dictionary],
        StoreLocal(store) => smallvec![store.value],
        Return(value) | Yield(value) | ExtractTag(value) => smallvec![*value],
        WithYielded(with) => smallvec![with.accessor, with.body],
        WithPlace(with) => smallvec![with.place, with.body],
        Block(block) => block.body.iter().copied().collect(),
        Assign(assign) => smallvec![assign.place, assign.value],
        Tuple(values) | Record(values) | Array(values) => values.iter().copied().collect(),
        Project(project) => smallvec![project.value],
        Variant(variant) => smallvec![variant.payload],
        Case(case) => std::iter::once(case.value)
            .chain(case.alternatives.iter().map(|(_, value)| *value))
            .chain(std::iter::once(case.default))
            .collect(),
        Loop(r#loop) => smallvec![r#loop.body],
        Break(r#break) => smallvec![r#break.value],
        FieldAccess(never)
        | TraitMethodApply(never)
        | GetTraitMethod(never)
        | GetTraitAssociatedConst(never)
        | GetTraitDictionary(never) => match *never {},
    }
}
