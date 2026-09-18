// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Logical initialization paths, before physical projections erase their field identities.

use std::collections::VecDeque;

use crate::{
    FxHashMap, define_id_type,
    mir::{
        Function, Operation, OperationKind, ParameterId, ParameterKind, Value, ValueId,
        role::{MirType, ValueRole, ValueRoles},
        terminator::TerminatorKind,
    },
    module::{ModuleEnv, ProjectionIndex, id::Id},
    std::value::{product_member_types, structural_variant},
    types::r#type::{Type, TypeKind},
};

/// Possible initialization states at a control-flow point.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum InitState {
    Absent,
    Live,
    MaybeLive,
}

impl InitState {
    fn join(self, other: Self) -> Self {
        if self == other { self } else { Self::MaybeLive }
    }
}

use InitState::{Absent, Live, MaybeLive};

define_id_type!(
    /// Identity of a logical storage node in this function's initialization analysis.
    LogicalPlaceId
);

/// A product member or variant payload along a logical storage path.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum Field {
    Product(ProjectionIndex),
    Payload(Type),
}

/// An initialization-state assignment, copied from another place or set explicitly.
#[derive(Clone, Copy)]
pub(super) enum Update {
    Copy(LogicalPlaceId),
    Set(InitState),
}

/// A logical storage node whose initialization is tracked independently of its physical address.
pub(super) struct Place {
    pub ty: Type,
    pub parent: Option<LogicalPlaceId>,
    pub children: Vec<(Field, LogicalPlaceId)>,
    pub variant: bool,
    /// Only generated structural destructors may be expanded for a partial receiver.
    pub structural: bool,
    pub initial: InitState,
    /// Descendant writes can create partial values; whole-place transfers cannot.
    pub split: bool,
}

/// Logical storage paths and MIR definitions used to derive initialization-state transitions.
pub(super) struct Places {
    pub nodes: Vec<Place>,
    pub values: FxHashMap<Value, LogicalPlaceId>,
    pub definitions: FxHashMap<ValueId, Operation>,
}

impl Places {
    fn root(
        &mut self,
        value: Value,
        ty: Type,
        initial: InitState,
        env: ModuleEnv<'_>,
    ) -> LogicalPlaceId {
        let id = self.add(ty, None, initial, env);
        self.values.insert(value, id);
        id
    }

    fn add(
        &mut self,
        ty: Type,
        parent: Option<LogicalPlaceId>,
        initial: InitState,
        env: ModuleEnv<'_>,
    ) -> LogicalPlaceId {
        let id = LogicalPlaceId::from_index(self.nodes.len());
        let structural = match &*ty.data() {
            TypeKind::Named(named) => !env.type_def(named.def).has_custom_value_impl,
            _ => true,
        };
        self.nodes.push(Place {
            ty,
            parent,
            initial,
            children: vec![],
            variant: structural_variant(ty, &env).is_some(),
            structural,
            split: false,
        });
        id
    }

    fn field(
        &mut self,
        base: LogicalPlaceId,
        field: Field,
        ty: Type,
        env: ModuleEnv<'_>,
    ) -> LogicalPlaceId {
        if let Some((_, id)) = self.nodes[base.as_index()]
            .children
            .iter()
            .find(|(f, _)| *f == field)
        {
            return *id;
        }
        let initial = self.nodes[base.as_index()].initial;
        if matches!(field, Field::Product(_)) && self.nodes[base.as_index()].children.is_empty() {
            let members = product_member_types(self.nodes[base.as_index()].ty, &env)
                .expect("logical product projection must have a product shape");
            for (index, ty) in members.into_iter().enumerate() {
                let id = self.add(ty, Some(base), initial, env);
                self.nodes[base.as_index()]
                    .children
                    .push((Field::Product(ProjectionIndex::from_index(index)), id));
            }
            return self.nodes[base.as_index()]
                .children
                .iter()
                .find(|(f, _)| *f == field)
                .unwrap()
                .1;
        }
        let id = self.add(ty, Some(base), initial, env);
        self.nodes[base.as_index()].children.push((field, id));
        id
    }

    pub fn of(body: &Function, env: ModuleEnv<'_>) -> Self {
        let mut result = Self {
            nodes: vec![],
            values: FxHashMap::default(),
            definitions: FxHashMap::default(),
        };
        for (index, parameter) in body.parameters().iter().enumerate() {
            if parameter.kind != ParameterKind::Dictionary {
                let initial = if parameter.kind == ParameterKind::Return {
                    Absent
                } else {
                    Live
                };
                result.root(
                    Value::Parameter(ParameterId::from_index(index)),
                    parameter.ty,
                    initial,
                    env,
                );
            }
        }
        let operations = body
            .blocks()
            .flat_map(|b| {
                let b = body.block(b);
                b.operations().iter().chain(match &b.terminator().kind {
                    TerminatorKind::Invoke { operation, .. } => Some(operation),
                    _ => None,
                })
            })
            .collect::<Vec<_>>();
        let roles = ValueRoles::derive(body);
        for op in &operations {
            if let Some(id) = op.result_id() {
                if matches!(
                    op.kind,
                    OperationKind::DictEntry { .. }
                        | OperationKind::BuildDictionary { .. }
                        | OperationKind::Variant { .. }
                ) {
                    result.definitions.insert(id, (*op).clone());
                }
                let value = Value::Register(id);
                if matches!(op.kind, OperationKind::Subfield { .. }) {
                    continue;
                }
                if let Some(role) = roles.get(&value, body.constants()) {
                    let ty = match &*role {
                        ValueRole::Place(MirType::Lowered(ty)) => Some(*ty),
                        ValueRole::OpenProjection { yielded, .. } => Some(*yielded),
                        ValueRole::Materialized(MirType::Pointer(ty)) => match &**ty {
                            MirType::Lowered(ty) => Some(*ty),
                            _ => None,
                        },
                        _ => None,
                    };
                    if let Some(ty) = ty {
                        let initial = if matches!(
                            op.kind,
                            OperationKind::Alloca { .. } | OperationKind::RuntimeAlloc { .. }
                        ) {
                            Absent
                        } else {
                            // Pointees are assumed complete; aliases must not track ownership independently.
                            Live
                        };
                        result.root(value, ty, initial, env);
                    }
                }
            }
        }
        // SSA block numbering need not be dominance order.
        loop {
            let mut changed = false;
            for op in &operations {
                let OperationKind::Subfield {
                    ty,
                    variant_payload,
                    ..
                } = op.kind
                else {
                    continue;
                };
                let value = Value::Register(op.result_id().unwrap());
                if result.values.contains_key(&value) {
                    continue;
                }
                let Some(&base) = result.values.get(&op.operands[0]) else {
                    continue;
                };
                let field = if variant_payload {
                    Field::Payload(ty)
                } else {
                    let Value::Constant(index) = op.operands[1] else {
                        panic!("dynamic logical product index");
                    };
                    Field::Product(ProjectionIndex::from_index(
                        *body
                            .constant(index)
                            .representation
                            .as_primitive_ty::<isize>()
                            .unwrap() as usize,
                    ))
                };
                let id = result.field(base, field, ty, env);
                result.values.insert(value, id);
                changed = true;
            }
            if !changed {
                break;
            }
        }
        // Installing a shell starts a partial payload even if construction fails before its
        // first projection. Keep that path explicit so Replace cannot inherit a live shell's
        // state for an absent, otherwise unobserved payload.
        for op in &operations {
            if matches!(op.kind, OperationKind::Store)
                && let Value::Register(value) = op.operands[0]
                && let Some(Operation {
                    kind: OperationKind::Variant { metadata, .. },
                    ..
                }) = result.definitions.get(&value)
                && metadata.payload_ty != Type::unit()
                && let Some(&base) = result.values.get(&op.operands[1])
            {
                let ty = metadata.payload_ty;
                result.field(base, Field::Payload(ty), ty, env);
            }
        }
        // Only the displaced value can be partial. Copy its paths into the whole replacement
        // local, never the reverse: symmetric merging can unfold recursive types indefinitely.
        // Since receivers are roots, propagation cannot increase the maximum path depth.
        let replacements = operations
            .iter()
            .filter(|op| matches!(op.kind, OperationKind::Replace))
            .filter_map(|op| {
                Some((
                    *result.values.get(&op.operands[0])?,
                    *result.values.get(&op.operands[1])?,
                ))
            })
            .collect::<Vec<_>>();
        for &(a, b) in &replacements {
            assert!(
                result.nodes[a.as_index()].parent.is_none(),
                "replace replacement must be a whole logical place"
            );
            let contains = |ancestor: LogicalPlaceId, mut place: LogicalPlaceId| {
                loop {
                    if ancestor == place {
                        break true;
                    }
                    let Some(parent) = result.nodes[place.as_index()].parent else {
                        break false;
                    };
                    place = parent;
                }
            };
            assert!(
                !contains(a, b) && !contains(b, a),
                "replace requires disjoint logical places"
            );
        }
        loop {
            let count = result.nodes.len();
            for &(a, b) in &replacements {
                result.inherit_paths(a, b, env);
            }
            if result.nodes.len() == count {
                break;
            }
        }
        // Record fields that construction, movement or replacement can initialize independently.
        for op in &operations {
            for id in result.writes(op) {
                let mut parent = result.nodes[id.as_index()].parent;
                while let Some(id) = parent {
                    result.nodes[id.as_index()].split = true;
                    parent = result.nodes[id.as_index()].parent;
                }
            }
        }
        loop {
            let count = result.nodes.iter().filter(|n| n.split).count();
            for &(a, b) in &replacements {
                result.inherit_splits(a, b);
            }
            if result.nodes.iter().filter(|n| n.split).count() == count {
                break;
            }
        }
        result
    }

    fn inherit_paths(
        &mut self,
        receiver: LogicalPlaceId,
        displaced: LogicalPlaceId,
        env: ModuleEnv<'_>,
    ) {
        if receiver == displaced {
            return;
        }
        for (field, child) in self.nodes[displaced.as_index()].children.clone() {
            let other = self.field(receiver, field, self.nodes[child.as_index()].ty, env);
            self.inherit_paths(other, child, env);
        }
    }

    fn inherit_splits(&mut self, a: LogicalPlaceId, b: LogicalPlaceId) {
        if a == b {
            return;
        }
        self.nodes[a.as_index()].split |= self.nodes[b.as_index()].split;
        for (field, child) in self.nodes[b.as_index()].children.clone() {
            let other = self.nodes[a.as_index()]
                .children
                .iter()
                .find(|(f, _)| *f == field)
                .unwrap()
                .1;
            self.inherit_splits(other, child);
        }
    }

    fn writes(&self, op: &Operation) -> Vec<LogicalPlaceId> {
        let mut writes = vec![];
        self.visit_effects(op, true, |id, _| writes.push(id));
        writes
    }

    pub fn set(&self, state: &mut [InitState], id: LogicalPlaceId, value: InitState) {
        state[id.as_index()] = value;
        for &(_, child) in &self.nodes[id.as_index()].children {
            self.set(state, child, value);
        }
    }

    /// Whole storage is atomic unless independent descendant writes split its state.
    pub fn status(&self, state: &[InitState], id: LogicalPlaceId) -> InitState {
        let node = &self.nodes[id.as_index()];
        if !node.split || node.children.is_empty() {
            return state[id.as_index()];
        }
        let mut live = !node.variant || state[id.as_index()] == Live;
        let mut absent = !node.variant || state[id.as_index()] == Absent;
        for &(_, child) in &node.children {
            let status = self.status(state, child);
            live &= status == Live;
            absent &= status == Absent;
        }
        if live {
            Live
        } else if absent || node.variant && state[id.as_index()] == Absent {
            Absent
        } else {
            MaybeLive
        }
    }

    pub fn partial(&self, state: &[InitState], id: LogicalPlaceId) -> bool {
        self.nodes[id.as_index()].structural
            && self.nodes[id.as_index()].split
            && !self.nodes[id.as_index()].children.is_empty()
            && self.status(state, id) == MaybeLive
    }

    /// Whole-place effects shared by split discovery, dataflow, and flag emission.
    fn visit_effects(
        &self,
        op: &Operation,
        success: bool,
        mut visit: impl FnMut(LogicalPlaceId, Update),
    ) {
        // A register can denote a new place on each loop iteration. Reset only roots, not
        // projections (which share their owner's state), and only after successful evaluation.
        if success
            && let Some(result) = op.result_id()
            && let Some(&id) = self.values.get(&Value::Register(result))
            && self.nodes[id.as_index()].parent.is_none()
        {
            visit(id, Update::Set(self.nodes[id.as_index()].initial));
        }
        let mut effect = |value: &Value, update| {
            if let Some(&id) = self.values.get(value) {
                visit(id, update);
            }
        };
        use OperationKind::*;
        match &op.kind {
            Store => {
                effect(&op.operands[1], Update::Set(Live));
                if let Value::Register(id) = op.operands[0]
                    && let Some(Operation {
                        kind: Variant { metadata, .. },
                        ..
                    }) = self.definitions.get(&id)
                    && let Some(&base) = self.values.get(&op.operands[1])
                {
                    for &(field, child) in &self.nodes[base.as_index()].children {
                        if field == Field::Payload(metadata.payload_ty)
                            && metadata.payload_ty != Type::unit()
                        {
                            visit(child, Update::Set(Absent));
                        }
                    }
                }
            }
            Memcpy | Move | MoveBytes { .. }
                if self.same_place(&op.operands[0], &op.operands[1]) => {}
            Memcpy | Move | MoveBytes { .. } => {
                effect(&op.operands[1], Update::Set(Live));
                if matches!(op.kind, Move | MoveBytes { .. }) {
                    effect(&op.operands[0], Update::Set(Absent));
                }
            }
            Replace => {
                // The semantic verifier requires a complete owned replacement. Only the
                // displaced destination may be partial; this is not a symmetric state swap.
                let displaced = self
                    .values
                    .get(&op.operands[1])
                    .copied()
                    .map_or(Update::Set(Live), Update::Copy);
                effect(&op.operands[0], displaced);
                effect(&op.operands[1], Update::Set(Live));
            }
            Drop { .. } | DropInitialized { .. } | DropSubscriptEnv | Clear => {
                effect(&op.operands[0], Update::Set(Absent))
            }
            BuildClosure {
                num_hidden_dicts,
                has_env_dict,
                ..
            } => {
                let end = op.operands.len() - usize::from(*has_env_dict);
                for capture in &op.operands[*num_hidden_dicts as usize..end] {
                    effect(capture, Update::Set(Absent));
                }
            }
            Clone { .. } if success => effect(&op.operands[1], Update::Set(Live)),
            BuildArray { .. } if success => effect(op.operands.last().unwrap(), Update::Set(Live)),
            Call { ty, metadata } => {
                if let Some(metadata) = metadata {
                    let start = op.operands.len()
                        - ty.fn_ty.args.len()
                        - usize::from(ty.result_convention.has_result_place());
                    for index in metadata.owned_arguments.iter_ones() {
                        effect(&op.operands[start + index], Update::Set(Absent));
                    }
                }
                if success && ty.result_convention.has_result_place() {
                    effect(op.operands.last().unwrap(), Update::Set(Live));
                }
            }
            _ => (),
        }
    }

    /// Expand subtree effects into simultaneous scalar flag updates.
    pub fn updates(&self, op: &Operation, success: bool) -> Vec<(LogicalPlaceId, Update)> {
        let mut updates = vec![];
        self.visit_effects(op, success, |id, update| match update {
            Update::Set(value) => self.each(id, &mut |id| updates.push((id, Update::Set(value)))),
            Update::Copy(source) => self.copy_state(id, source, &mut updates),
        });
        updates
    }

    fn same_place(&self, a: &Value, b: &Value) -> bool {
        a == b
            || self
                .values
                .get(a)
                .zip(self.values.get(b))
                .is_some_and(|(a, b)| a == b)
    }

    fn copy_state(
        &self,
        receiver: LogicalPlaceId,
        displaced: LogicalPlaceId,
        out: &mut Vec<(LogicalPlaceId, Update)>,
    ) {
        out.push((receiver, Update::Copy(displaced)));
        for &(field, child) in &self.nodes[receiver.as_index()].children {
            if let Some(&(_, source)) = self.nodes[displaced.as_index()]
                .children
                .iter()
                .find(|(f, _)| *f == field)
            {
                self.copy_state(child, source, out);
            } else {
                // This path has no independent writes in the displaced value. Its entire
                // subtree inherits the enclosing state; do not resolve deeper fields against
                // the wrong ancestor. Paths need only propagate from displaced to receiver.
                self.each(child, &mut |id| out.push((id, Update::Copy(displaced))));
            }
        }
    }

    pub fn each(&self, id: LogicalPlaceId, f: &mut impl FnMut(LogicalPlaceId)) {
        f(id);
        for &(_, child) in &self.nodes[id.as_index()].children {
            self.each(child, f);
        }
    }

    pub fn transfer(&self, state: &mut [InitState], op: &Operation, success: bool) {
        let mut writes = self.updates(op, success);
        // Snapshot every source before assigning any target (notably for Replace).
        for (_, value) in &mut writes {
            if let Update::Copy(source) = *value {
                *value = Update::Set(state[source.as_index()]);
            }
        }
        for (id, value) in writes {
            let Update::Set(value) = value else {
                unreachable!()
            };
            state[id.as_index()] = value;
        }
    }

    pub fn analyze(&self, body: &Function) -> Vec<Option<Vec<InitState>>> {
        let mut entries = vec![None; body.blocks().count()];
        entries[body.entry().as_index()] =
            Some(self.nodes.iter().map(|n| n.initial).collect::<Vec<_>>());
        let mut pending = VecDeque::from([body.entry()]);
        let mut queued = vec![false; entries.len()];
        queued[body.entry().as_index()] = true;
        while let Some(id) = pending.pop_front() {
            queued[id.as_index()] = false;
            let mut state = entries[id.as_index()].clone().unwrap();
            let block = body.block(id);
            for op in block.operations() {
                self.transfer(&mut state, op, true);
            }
            let edges = match &block.terminator().kind {
                TerminatorKind::Invoke {
                    operation,
                    normal,
                    error,
                } => {
                    let mut failed = state.clone();
                    self.transfer(&mut failed, operation, false);
                    self.transfer(&mut state, operation, true);
                    vec![(*normal, state), (*error, failed)]
                }
                TerminatorKind::Goto { target } => vec![(*target, state)],
                TerminatorKind::CondBr {
                    condition,
                    then_target,
                    else_target,
                } => {
                    let mut yes = state.clone();
                    if let Value::Register(condition) = condition
                        && let Some(op) = block.operations().last()
                        && op.result_id() == Some(*condition)
                        && matches!(op.kind, OperationKind::IsInitialized)
                        && let Some(&place) = self.values.get(&op.operands[0])
                    {
                        // Only refine an immediately preceding observation: intervening writes
                        // could make an older initialization query stale.
                        // Variant queries concern their shell, not the payload being constructed.
                        if self.nodes[place.as_index()].variant {
                            yes[place.as_index()] = Live;
                            state[place.as_index()] = Absent;
                        } else {
                            self.set(&mut yes, place, Live);
                        }
                    }
                    vec![(*then_target, yes), (*else_target, state)]
                }
                TerminatorKind::SwitchVariant { cases, default, .. } => cases
                    .iter()
                    .map(|(_, b)| (*b, state.clone()))
                    .chain([(*default, state.clone())])
                    .collect(),
                TerminatorKind::Yield { resume, .. } => vec![(*resume, state)],
                _ => vec![],
            };
            for (target, state) in edges {
                let old = &mut entries[target.as_index()];
                let changed = if let Some(old) = old {
                    let mut changed = false;
                    for (old, value) in old.iter_mut().zip(&state) {
                        let joined = old.join(*value);
                        if joined != *old {
                            *old = joined;
                            changed = true;
                        }
                    }
                    changed
                } else {
                    *old = Some(state);
                    true
                };
                if changed && !queued[target.as_index()] {
                    queued[target.as_index()] = true;
                    pending.push_back(target);
                }
            }
        }
        entries
    }
}
