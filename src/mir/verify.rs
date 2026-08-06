// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Derived structural and ownership verification for MIR functions.
//!
//! The verifier deliberately keeps initialization/drop state out of [`Function`]. MIR operations
//! (`store`, `move`, `drop`, `clear`, …) are the source of truth; this module derives their effects
//! per function and checks them before execution. A later backend may lower the same abstract state
//! to concrete drop flags without exposing those flags to optimization-oriented MIR.

use std::collections::VecDeque;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    format::FormatWith,
    mir::{
        self, BlockId, Function, Operation, OperationKind, OperationResult, ParameterKind,
        operation::SourceFallibility, terminator::TerminatorKind,
    },
    module::{ModuleEnv, id::Id},
    types::{
        effects::{Effect, PrimitiveEffect},
        trait_solver::TraitSolverProbe,
        r#type::{CallImplType, Type, TypeKind},
        type_like::TypeLike,
    },
};

fn call_type_is_fallible(ty: &CallImplType) -> bool {
    ty.effects()
        .contains(Effect::Primitive(PrimitiveEffect::Fallible))
        || ty.effects().has_variables()
}

/// Verifies all machine-checkable per-function MIR contracts.
///
/// This is intentionally intraprocedural: calls are checked through the uniform by-pointer boundary
/// contract, so lazy lowering does not force the callee's MIR body to exist.
pub(crate) fn verify_function(func: &Function, env: ModuleEnv<'_>) {
    let solver = TraitSolverProbe::from_module(env.current, env.modules);
    Verifier::new(func, env, solver).verify();
}

/// Clones an interned type descriptor and explicitly releases the universe read lock.
///
/// Several verifier operations recursively intern instantiated types. Keeping a [`Type::data`]
/// guard alive across those operations would attempt to acquire the universe write lock while the
/// same thread still holds a read lock.
fn cloned_type_kind(ty: Type) -> TypeKind {
    let guard = ty.data();
    let kind = guard.clone();
    drop(guard);
    kind
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum MirType {
    Lowered(Type),
    Pointer(Box<MirType>),
}

impl MirType {
    fn format(&self, env: &ModuleEnv<'_>) -> String {
        match self {
            Self::Lowered(ty) => ty.format_with(env).to_string(),
            Self::Pointer(pointee) => format!("*{}", pointee.format(env)),
        }
    }

    fn representation_compatible(&self, other: &Self, env: &ModuleEnv<'_>) -> bool {
        match (self, other) {
            (Self::Lowered(left), Self::Lowered(right)) => {
                lowered_representations_compatible(*left, *right, env, &mut FxHashSet::default())
            }
            (Self::Pointer(left), Self::Pointer(right)) => {
                left.representation_compatible(right, env)
            }
            _ => false,
        }
    }

    fn is_fully_concrete(&self) -> bool {
        match self {
            Self::Lowered(ty) => ty.is_constant(),
            Self::Pointer(pointee) => pointee.is_fully_concrete(),
        }
    }
}

fn lowered_representations_compatible(
    left: Type,
    right: Type,
    env: &ModuleEnv<'_>,
    active: &mut FxHashSet<(Type, Type)>,
) -> bool {
    if left == right {
        return true;
    }
    if !active.insert((left, right)) {
        // Recursive occurrences are represented indirectly, so reaching the same comparison again
        // means both sides have the same pointer-shaped recursion boundary.
        return true;
    }

    let left_kind = cloned_type_kind(left);
    let right_kind = cloned_type_kind(right);
    let result = match (left_kind, right_kind) {
        (TypeKind::Named(named), _) => {
            lowered_representations_compatible(named.instantiated_shape(env), right, env, active)
        }
        (_, TypeKind::Named(named)) => {
            lowered_representations_compatible(left, named.instantiated_shape(env), env, active)
        }
        (TypeKind::Function(_), TypeKind::Function(_))
        | (TypeKind::Subscript(_), TypeKind::Subscript(_)) => true,
        (TypeKind::Native(left), TypeKind::Native(right)) => {
            left.bare_ty == right.bare_ty
                && left.arguments.len() == right.arguments.len()
                && left
                    .arguments
                    .iter()
                    .zip(&right.arguments)
                    .all(|(left, right)| {
                        lowered_representations_compatible(*left, *right, env, active)
                    })
        }
        (TypeKind::Tuple(left), TypeKind::Tuple(right)) => {
            left.len() == right.len()
                && left.iter().zip(&right).all(|(left, right)| {
                    lowered_representations_compatible(*left, *right, env, active)
                })
        }
        (TypeKind::Record(left), TypeKind::Record(right))
        | (TypeKind::Variant(left), TypeKind::Variant(right)) => {
            left.len() == right.len()
                && left
                    .iter()
                    .zip(&right)
                    .all(|((left_name, left), (right_name, right))| {
                        left_name == right_name
                            && lowered_representations_compatible(*left, *right, env, active)
                    })
        }
        _ => false,
    };
    active.remove(&(left, right));
    result
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum ValueRole {
    Materialized(MirType),
    Place(MirType),
    Dictionary,
    Subscript,
    Function,
    Pattern,
    StackMarker,
    /// A yielded place paired with the accessor contract whose slide must be ended exactly once.
    OpenProjection {
        yielded: Type,
        accessor: CallImplType,
    },
}

impl ValueRole {
    fn is_place_operand(&self) -> bool {
        matches!(
            self,
            Self::Place(_) | Self::Materialized(MirType::Pointer(_)) | Self::OpenProjection { .. }
        )
    }

    fn is_materialized(&self) -> bool {
        matches!(
            self,
            Self::Materialized(_) | Self::Function | Self::Subscript
        )
    }

    fn is_evidence(&self) -> bool {
        matches!(self, Self::Dictionary | Self::Subscript | Self::Place(_))
    }
}

/// The possible ownership states of one storage leaf at a program point.
///
/// A bitset is more precise than a four-way enum at control-flow joins: for example
/// `ABSENT | LIVE_NO_DROP` is safe to overwrite, while `ABSENT | LIVE_NEEDS_DROP` is not.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct LeafState(u8);

impl LeafState {
    const UNALLOCATED: Self = Self(1 << 0);
    const ABSENT: Self = Self(1 << 1);
    const LIVE_NO_DROP: Self = Self(1 << 2);
    const LIVE_NEEDS_DROP: Self = Self(1 << 3);

    fn join(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    fn may_be_unallocated(self) -> bool {
        self.0 & Self::UNALLOCATED.0 != 0
    }

    fn may_need_drop(self) -> bool {
        self.0 & Self::LIVE_NEEDS_DROP.0 != 0
    }

    fn may_be_absent(self) -> bool {
        self.0 & Self::ABSENT.0 != 0
    }

    fn may_be_live(self) -> bool {
        self.0 & (Self::LIVE_NO_DROP.0 | Self::LIVE_NEEDS_DROP.0) != 0
    }

    fn is_definitely_live(self) -> bool {
        self.may_be_live() && !self.may_be_absent() && !self.may_be_unallocated()
    }

    fn is_definitely_unallocated(self) -> bool {
        self == Self::UNALLOCATED
    }

    fn may_be_overwritten_without_drop(self) -> bool {
        !self.may_be_unallocated() && !self.may_need_drop()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct StorageState {
    ty: Type,
    state: LeafState,
    fields: Vec<StorageState>,
}

impl StorageState {
    fn shaped(ty: Type, state: LeafState, env: &ModuleEnv<'_>, active: &mut Vec<Type>) -> Self {
        if active.contains(&ty) {
            return Self {
                ty,
                state,
                fields: vec![],
            };
        }
        active.push(ty);
        let kind = cloned_type_kind(ty);
        let field_tys = match kind {
            TypeKind::Tuple(fields) => Some(fields),
            TypeKind::Record(fields) => {
                Some(fields.into_iter().map(|(_, ty)| ty).collect::<Vec<_>>())
            }
            TypeKind::Named(named) => {
                let def = env.type_def(named.def);
                (!def.has_custom_value_impl).then(|| {
                    let shape =
                        def.instantiated_shape_with_effects(&named.params, &named.effect_params);
                    match cloned_type_kind(shape) {
                        TypeKind::Tuple(fields) => fields,
                        TypeKind::Record(fields) => {
                            fields.into_iter().map(|(_, ty)| ty).collect::<Vec<_>>()
                        }
                        _ => vec![],
                    }
                })
            }
            _ => None,
        };
        let fields = field_tys
            .filter(|fields| !fields.is_empty())
            .map(|fields| {
                fields
                    .into_iter()
                    .map(|field| Self::shaped(field, state, env, active))
                    .collect()
            })
            .unwrap_or_default();
        active.pop();
        Self { ty, state, fields }
    }

    fn shape_mismatch(&self, other: &Self, path: &mut Vec<usize>) -> Option<(Type, Type)> {
        if self.ty != other.ty || self.fields.len() != other.fields.len() {
            return Some((self.ty, other.ty));
        }
        for (index, (field, other)) in self.fields.iter().zip(&other.fields).enumerate() {
            path.push(index);
            if let Some(mismatch) = field.shape_mismatch(other, path) {
                return Some(mismatch);
            }
            path.pop();
        }
        None
    }

    fn join(&mut self, other: &Self) -> bool {
        debug_assert_eq!(self.ty, other.ty);
        debug_assert_eq!(self.fields.len(), other.fields.len());
        let joined = self.state.join(other.state);
        let mut changed = joined != self.state;
        self.state = joined;
        for (field, other) in self.fields.iter_mut().zip(&other.fields) {
            changed |= field.join(other);
        }
        changed
    }

    fn set_all(&mut self, state: LeafState) {
        self.state = state;
        for field in &mut self.fields {
            field.set_all(state);
        }
    }

    fn recompute(&mut self) {
        if self.fields.is_empty() {
            return;
        }
        let mut state = LeafState(0);
        for field in &mut self.fields {
            field.recompute();
            state = state.join(field.state);
        }
        self.state = state;
    }

    fn at_path(&self, path: &[usize]) -> Option<&Self> {
        let Some((&first, rest)) = path.split_first() else {
            return Some(self);
        };
        self.fields.get(first)?.at_path(rest)
    }

    fn at_path_mut(&mut self, path: &[usize]) -> Option<&mut Self> {
        let Some((&first, rest)) = path.split_first() else {
            return Some(self);
        };
        self.fields.get_mut(first)?.at_path_mut(rest)
    }

    fn tracked_prefix_len(&self, path: &[usize]) -> usize {
        let mut current = self;
        for (depth, index) in path.iter().copied().enumerate() {
            let Some(field) = current.fields.get(index) else {
                return depth;
            };
            current = field;
        }
        path.len()
    }

    fn set_path_all(&mut self, path: &[usize], state: LeafState) -> bool {
        let Some(target) = self.at_path_mut(path) else {
            // Variants and other opaque representations retain ownership in their shell. Their
            // payload projections cannot be tracked field-wise here, but must not erase that shell
            // obligation.
            return false;
        };
        target.set_all(state);
        self.recompute();
        true
    }

    fn replace_path(&mut self, path: &[usize], replacement: &Self) -> bool {
        let Some(target) = self.at_path_mut(path) else {
            return false;
        };
        debug_assert_eq!(target.ty, replacement.ty);
        *target = replacement.clone();
        self.recompute();
        true
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct AnalysisState {
    roots: Vec<StorageState>,
    /// The live allocation-site snapshot captured by each `stack_save` register.
    markers: FxHashMap<mir::Value, Vec<bool>>,
    /// Scoped accessor projections whose slide remains to be executed.
    open_projections: FxHashSet<mir::Value>,
}

impl AnalysisState {
    fn has_same_allocation_frontier(&self, other: &Self) -> bool {
        self.roots.iter().zip(&other.roots).all(|(left, right)| {
            left.state.may_be_unallocated() == right.state.may_be_unallocated()
        })
    }

    fn join_roots(&mut self, other: &Self, func: &Function, env: &ModuleEnv<'_>) -> bool {
        debug_assert_eq!(self.markers, other.markers);
        debug_assert_eq!(
            self.open_projections, other.open_projections,
            "MIR function `{}`: incompatible open-projection obligations at CFG join",
            func.name
        );
        debug_assert!(self.has_same_allocation_frontier(other));
        let mut changed = false;
        for (index, (root, other)) in self.roots.iter_mut().zip(&other.roots).enumerate() {
            let mut path = Vec::new();
            if let Some((left, right)) = root.shape_mismatch(other, &mut path) {
                panic!(
                    "MIR function `{}`: storage root {index} has incompatible types at path \
                     {path:?} across a control-flow join: {} versus {}\n{}",
                    func.name,
                    left.format_with(env),
                    right.format_with(env),
                    func.format_with(env)
                );
            }
            changed |= root.join(other);
        }
        changed
    }
}

#[derive(Clone, Debug)]
enum LocalPlace {
    Root {
        root: usize,
        path: Option<Vec<usize>>,
    },
    External,
}

#[derive(Clone, Copy)]
enum EdgeKind {
    Normal,
    Error,
}

/// Source-failure state carried implicitly while traversing the explicit MIR error CFG.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FailureState {
    Normal,
    Propagating,
    FailedDuringCleanup,
}

/// Constant-time dominance queries over the reachable node CFG.
///
/// Immediate dominators are computed with the Cooper-Harvey-Kennedy algorithm, then the resulting
/// dominator tree is numbered in depth-first order. A node dominates another exactly when its tree
/// interval contains the other's interval.
struct NodeDominance {
    preorder: Vec<usize>,
    postorder: Vec<usize>,
}

impl NodeDominance {
    const UNREACHABLE: usize = usize::MAX;

    fn is_reachable(&self, node: usize) -> bool {
        self.preorder[node] != Self::UNREACHABLE
    }

    fn dominates(&self, definition: usize, usage: usize) -> bool {
        self.is_reachable(definition)
            && self.is_reachable(usage)
            && self.preorder[definition] <= self.preorder[usage]
            && self.postorder[usage] <= self.postorder[definition]
    }
}

fn intersect_dominator_paths(
    mut left: usize,
    mut right: usize,
    immediate_dominator: &[Option<usize>],
    reverse_postorder_index: &[usize],
) -> usize {
    while left != right {
        while reverse_postorder_index[left] > reverse_postorder_index[right] {
            left = immediate_dominator[left]
                .expect("dominance intersection must stay on the known dominator tree");
        }
        while reverse_postorder_index[right] > reverse_postorder_index[left] {
            right = immediate_dominator[right]
                .expect("dominance intersection must stay on the known dominator tree");
        }
    }
    left
}

struct RootInfo {
    value: mir::Value,
    ty: Type,
    /// Whether every ownership-relevant subplace of this root is represented precisely by
    /// `StorageState`. Opaque native/custom/variant interiors are still checked at individual
    /// operations, but cannot prove whole-frame absence at exit.
    exact: bool,
}

type NodeId = usize;

#[derive(Clone, Copy)]
enum NodeLocation {
    Operation { block: BlockId, index: usize },
    Terminator { block: BlockId },
}

struct Verifier<'a> {
    func: &'a Function,
    env: ModuleEnv<'a>,
    solver: TraitSolverProbe<'a>,
    nodes: Vec<NodeLocation>,
    node_order: Vec<NodeId>,
    node_index: FxHashMap<NodeId, usize>,
    node_block: FxHashMap<NodeId, BlockId>,
    block_first: FxHashMap<BlockId, NodeId>,
    value_definition: FxHashMap<mir::ValueId, NodeId>,
    value_roles: FxHashMap<mir::Value, ValueRole>,
    roots: Vec<RootInfo>,
    root_index: FxHashMap<mir::Value, usize>,
    trivial_copy: FxHashMap<Type, bool>,
}

impl<'a> Verifier<'a> {
    fn new(func: &'a Function, env: ModuleEnv<'a>, solver: TraitSolverProbe<'a>) -> Self {
        Self {
            func,
            env,
            solver,
            nodes: vec![],
            node_order: vec![],
            node_index: FxHashMap::default(),
            node_block: FxHashMap::default(),
            block_first: FxHashMap::default(),
            value_definition: FxHashMap::default(),
            value_roles: FxHashMap::default(),
            roots: vec![],
            root_index: FxHashMap::default(),
            trivial_copy: FxHashMap::default(),
        }
    }

    fn verify(mut self) {
        self.verify_structure();
        self.collect_value_information();
        self.verify_operand_roles_and_dominance();
        self.verify_source_failure_flow();
        self.verify_register_consumption();
        self.verify_storage_ownership();
    }

    /// Verifies that source-error edges cannot rejoin normal execution and that each terminal form
    /// is reached with the error payload it consumes. The payload itself remains executor state;
    /// this analysis proves the control-flow protocol without storing a dynamic flag in MIR.
    fn verify_source_failure_flow(&self) {
        let mut inputs: FxHashMap<BlockId, FailureState> = FxHashMap::default();
        let mut worklist = VecDeque::from([self.func.entry()]);
        inputs.insert(self.func.entry(), FailureState::Normal);

        while let Some(block) = worklist.pop_front() {
            let state = inputs[&block];
            let terminator = &self.func.block(block).terminator().kind;
            let successors: Vec<(BlockId, FailureState)> = match terminator {
                TerminatorKind::Goto { target } => vec![(*target, state)],
                TerminatorKind::CondBr {
                    then_target,
                    else_target,
                    ..
                } => vec![(*then_target, state), (*else_target, state)],
                TerminatorKind::Invoke { normal, error, .. } => {
                    let error_state = match state {
                        FailureState::Normal => FailureState::Propagating,
                        FailureState::Propagating => FailureState::FailedDuringCleanup,
                        FailureState::FailedDuringCleanup => panic!(
                            "MIR function `{}` block {}: execution continues after a second source failure",
                            self.func.name,
                            block.as_u32()
                        ),
                    };
                    vec![(*normal, state), (*error, error_state)]
                }
                TerminatorKind::Yield { resume, .. } => {
                    assert_eq!(
                        state,
                        FailureState::Normal,
                        "MIR function `{}` block {}: yield reached while a source failure is propagating",
                        self.func.name,
                        block.as_u32()
                    );
                    vec![(*resume, state)]
                }
                TerminatorKind::Return => {
                    assert_eq!(
                        state,
                        FailureState::Normal,
                        "MIR function `{}` block {}: return reached while a source failure is propagating",
                        self.func.name,
                        block.as_u32()
                    );
                    vec![]
                }
                TerminatorKind::PropagateError => {
                    assert_eq!(
                        state,
                        FailureState::Propagating,
                        "MIR function `{}` block {}: propagate_error requires one in-flight source failure",
                        self.func.name,
                        block.as_u32()
                    );
                    vec![]
                }
                TerminatorKind::FailureDuringCleanup => {
                    assert_eq!(
                        state,
                        FailureState::FailedDuringCleanup,
                        "MIR function `{}` block {}: failure_during_cleanup requires two source failures",
                        self.func.name,
                        block.as_u32()
                    );
                    vec![]
                }
            };

            for (successor, successor_state) in successors {
                match inputs.entry(successor) {
                    std::collections::hash_map::Entry::Vacant(entry) => {
                        entry.insert(successor_state);
                        worklist.push_back(successor);
                    }
                    std::collections::hash_map::Entry::Occupied(entry) => assert_eq!(
                        *entry.get(),
                        successor_state,
                        "MIR function `{}` block {} joins normal and source-error control flow",
                        self.func.name,
                        successor.as_u32()
                    ),
                }
            }
        }
    }

    fn operation(&self, node: NodeId) -> Option<&Operation> {
        match self.nodes[node] {
            NodeLocation::Operation { block, index } => {
                Some(&self.func.block(block).operations()[index])
            }
            NodeLocation::Terminator { block } => match &self.func.block(block).terminator().kind {
                TerminatorKind::Invoke { operation, .. } => Some(operation),
                _ => None,
            },
        }
    }

    fn operands(&self, node: NodeId) -> &[mir::Value] {
        match self.nodes[node] {
            NodeLocation::Operation { .. } => &self.operation(node).unwrap().operands,
            NodeLocation::Terminator { block } => self.func.block(block).terminator().operands(),
        }
    }

    fn definition(&self, node: NodeId) -> Option<mir::Value> {
        self.operation(node)
            .and_then(Operation::result_id)
            .map(mir::Value::Register)
    }

    fn terminator(&self, node: NodeId) -> Option<&TerminatorKind> {
        match self.nodes[node] {
            NodeLocation::Operation { .. } => None,
            NodeLocation::Terminator { block } => Some(&self.func.block(block).terminator().kind),
        }
    }

    fn verify_structure(&mut self) {
        let block_ids: Vec<BlockId> = self.func.blocks().collect();
        let block_count = block_ids.len();
        let target_ok = |block: BlockId| block.as_index() < block_count;

        for &block in &block_ids {
            let first = self.nodes.len();
            self.block_first.insert(block, first);
            for (index, operation) in self.func.block(block).operations().iter().enumerate() {
                operation.verify();
                self.nodes.push(NodeLocation::Operation { block, index });
            }
            let node = self.nodes.len();
            self.nodes.push(NodeLocation::Terminator { block });

            match &self.func.block(block).terminator().kind {
                TerminatorKind::CondBr {
                    then_target,
                    else_target,
                    ..
                } => assert!(
                    target_ok(*then_target) && target_ok(*else_target),
                    "MIR function `{}` block {}: condbr targets a missing block",
                    self.func.name,
                    block.as_u32()
                ),
                TerminatorKind::Goto { target } => assert!(
                    target_ok(*target),
                    "MIR function `{}` block {}: branch targets a missing block",
                    self.func.name,
                    block.as_u32()
                ),
                TerminatorKind::Invoke {
                    operation,
                    normal,
                    error,
                } => {
                    operation.verify();
                    assert!(
                        target_ok(*normal) && target_ok(*error),
                        "MIR function `{}` block {}: invoke targets a missing block",
                        self.func.name,
                        block.as_u32()
                    );
                }
                TerminatorKind::Yield { resume, .. } => assert!(
                    target_ok(*resume),
                    "MIR function `{}` block {}: yield targets a missing resume block",
                    self.func.name,
                    block.as_u32()
                ),
                _ => {}
            }

            debug_assert_eq!(node + 1, self.nodes.len());
        }

        self.node_order.extend(0..self.nodes.len());
        for (index, &node) in self.node_order.iter().enumerate() {
            let block = match self.nodes[node] {
                NodeLocation::Operation { block, .. } | NodeLocation::Terminator { block } => block,
            };
            self.node_index.insert(node, index);
            self.node_block.insert(node, block);
        }
    }

    fn collect_value_information(&mut self) {
        for (index, parameter) in self.func.parameters().iter().enumerate() {
            let value = mir::Value::Parameter(mir::ParameterId::from_index(index));
            let role = match parameter.kind {
                ParameterKind::Dictionary => ValueRole::Dictionary,
                ParameterKind::Parameter(_) => ValueRole::Place(MirType::Lowered(parameter.ty)),
                ParameterKind::Return if self.func.result_convention().returns_place() => {
                    ValueRole::Place(MirType::Pointer(Box::new(MirType::Lowered(parameter.ty))))
                }
                ParameterKind::Return => ValueRole::Place(MirType::Lowered(parameter.ty)),
            };
            self.value_roles.insert(value, role);
        }

        for index in 0..self.node_order.len() {
            let node = self.node_order[index];
            let Some(value) = self.definition(node) else {
                continue;
            };
            let mir::Value::Register(value_id) = value else {
                unreachable!("node definitions are registers")
            };
            assert!(
                self.value_definition.insert(value_id, node).is_none(),
                "MIR function `{}`: value {value_id} has more than one definition",
                self.func.name
            );
            let value = mir::Value::Register(value_id);
            let operation = self.operation(node).unwrap();
            let role = match &operation.kind {
                OperationKind::Project { yielded, ty } => ValueRole::OpenProjection {
                    yielded: *yielded,
                    accessor: (**ty).clone(),
                },
                _ => self.resolve_result(operation.result()),
            };
            if let OperationKind::Alloca { ty } = operation.kind {
                let root = self.roots.len();
                let exact = self.storage_paths_are_exact(ty, &mut Vec::new());
                self.roots.push(RootInfo {
                    value: value.clone(),
                    ty,
                    exact,
                });
                self.root_index.insert(value.clone(), root);
            }
            self.value_roles.insert(value, role);
        }
    }

    fn resolve_result(&self, result: OperationResult) -> ValueRole {
        match result {
            OperationResult::Lowered(ty) => ValueRole::Materialized(MirType::Lowered(ty)),
            OperationResult::Pointer(pointee) => {
                ValueRole::Place(self.resolve_result_type(*pointee))
            }
            OperationResult::Pointee(pointer) => match self.resolve_result(*pointer) {
                ValueRole::Place(ty) => ValueRole::Materialized(ty),
                ValueRole::OpenProjection { yielded, .. } => {
                    ValueRole::Materialized(MirType::Lowered(yielded))
                }
                other => panic!(
                    "MIR function `{}`: `Pointee` result refers to non-place role {other:?}",
                    self.func.name
                ),
            },
            OperationResult::Same(value) => self.role(&value),
            OperationResult::StackMarker => ValueRole::StackMarker,
            OperationResult::Nothing => {
                panic!(
                    "MIR function `{}`: result-less node was defined",
                    self.func.name
                )
            }
        }
    }

    fn resolve_result_type(&self, result: OperationResult) -> MirType {
        match result {
            OperationResult::Lowered(ty) => MirType::Lowered(ty),
            OperationResult::Pointer(inner) => {
                MirType::Pointer(Box::new(self.resolve_result_type(*inner)))
            }
            OperationResult::Same(value) => match self.role(&value) {
                ValueRole::Materialized(ty) | ValueRole::Place(ty) => ty.clone(),
                ValueRole::OpenProjection { yielded, .. } => MirType::Lowered(yielded),
                other => panic!(
                    "MIR function `{}`: type requested for non-typed role {other:?}",
                    self.func.name
                ),
            },
            OperationResult::Pointee(pointer) => match self.resolve_result(*pointer) {
                ValueRole::Place(ty) => ty,
                ValueRole::OpenProjection { yielded, .. } => MirType::Lowered(yielded),
                other => panic!(
                    "MIR function `{}`: pointee type requested from {other:?}",
                    self.func.name
                ),
            },
            OperationResult::StackMarker | OperationResult::Nothing => panic!(
                "MIR function `{}`: non-value result used as a value type",
                self.func.name
            ),
        }
    }

    fn role(&self, value: &mir::Value) -> ValueRole {
        match value {
            mir::Value::Constant(id) => {
                ValueRole::Materialized(MirType::Lowered(self.func.constant(*id).ty))
            }
            mir::Value::Dictionary(_) => ValueRole::Dictionary,
            mir::Value::Subscript(_) => ValueRole::Subscript,
            mir::Value::Function(_) => ValueRole::Function,
            mir::Value::Pattern(_) => ValueRole::Pattern,
            mir::Value::Parameter(_) | mir::Value::Register(_) => self
                .value_roles
                .get(value)
                .unwrap_or_else(|| {
                    panic!(
                        "MIR function `{}`: undefined operand {value}",
                        self.func.name
                    )
                })
                .clone(),
        }
    }

    fn materialized_type(&self, value: &mir::Value) -> Option<MirType> {
        match value {
            mir::Value::Constant(id) => Some(MirType::Lowered(self.func.constant(*id).ty)),
            _ => match self.role(value) {
                ValueRole::Materialized(ty) => Some(ty),
                ValueRole::Function | ValueRole::Subscript => None,
                _ => None,
            },
        }
    }

    fn verify_operand_roles_and_dominance(&self) {
        let dominance = self.compute_instruction_dominance();
        for &node in &self.node_order {
            for operand in self.operands(node) {
                if let mir::Value::Register(definition) = operand {
                    let definition = self.value_definition[definition];
                    let dominance_definition = match self.terminator(definition) {
                        Some(TerminatorKind::Invoke { normal, .. }) => self.block_first[normal],
                        _ => definition,
                    };
                    let def_block = self.node_block[&dominance_definition];
                    let use_block = self.node_block[&node];
                    let definition_index = self.node_index[&dominance_definition];
                    let usage_index = self.node_index[&node];
                    let dominates = if dominance.is_reachable(usage_index) {
                        dominance.dominates(definition_index, usage_index)
                    } else {
                        // Unreachable node_order are not part of the dominance fixed point. Still
                        // reject a use preceding its definition within one unreachable block; no
                        // meaningful cross-block dominance relation exists without a path from the
                        // entry.
                        if def_block == use_block {
                            definition_index < usage_index
                        } else {
                            true
                        }
                    };
                    assert!(
                        dominates,
                        "MIR function `{}`: operand {operand} from block {} does not dominate \
                         node {} in block {}\n{}",
                        self.func.name,
                        def_block.as_u32(),
                        node,
                        use_block.as_u32(),
                        self.func.format_with(&self.env)
                    );
                }
            }
            self.verify_node_roles(node);
        }
    }

    fn verify_node_roles(&self, node: NodeId) {
        let operands = self.operands(node);
        let place = |index: usize| {
            assert!(
                self.role(&operands[index]).is_place_operand(),
                "MIR function `{}` node {}: operand {} must be a place, got {:?}",
                self.func.name,
                node,
                index,
                self.role(&operands[index])
            );
        };
        let value = |index: usize| {
            assert!(
                self.materialized_type(&operands[index]).is_some()
                    || self.role(&operands[index]).is_materialized(),
                "MIR function `{}` node {}: operand {} must be a materialized value, got {:?}",
                self.func.name,
                node,
                index,
                self.role(&operands[index])
            );
        };
        let evidence = |index: usize| {
            assert!(
                self.role(&operands[index]).is_evidence(),
                "MIR function `{}` node {}: operand {} must be evidence, got {:?}",
                self.func.name,
                node,
                index,
                self.role(&operands[index])
            );
        };

        let Some(whole) = self.operation(node) else {
            match self.terminator(node).unwrap() {
                TerminatorKind::CondBr { .. } => value(0),
                TerminatorKind::Yield { .. } => place(0),
                TerminatorKind::Goto { .. }
                | TerminatorKind::Return
                | TerminatorKind::PropagateError
                | TerminatorKind::FailureDuringCleanup => {}
                TerminatorKind::Invoke { .. } => unreachable!("invoke exposes its operation"),
            }
            return;
        };

        let invoked = matches!(self.terminator(node), Some(TerminatorKind::Invoke { .. }));
        assert_eq!(
            invoked,
            self.operation_is_source_fallible(whole),
            "MIR function `{}` node {}: source fallibility and Invoke form disagree",
            self.func.name,
            node
        );

        match &whole.kind {
            OperationKind::Alloca { .. } => {
                if !operands.is_empty() {
                    evidence(0);
                }
            }
            OperationKind::AllocaPlace { .. }
            | OperationKind::Variant { .. }
            | OperationKind::StackSave
            | OperationKind::CheckCallDepth
            | OperationKind::CheckFuel => {}
            OperationKind::Call { ty, instantiation } => {
                self.verify_instantiation(node, &operands[0], ty, instantiation.as_deref());
                let visible_start = operands
                    .len()
                    .checked_sub(ty.fn_ty.args.len() + 1)
                    .filter(|start| *start >= 1)
                    .unwrap_or_else(|| {
                        panic!(
                            "MIR function `{}` node {}: call has too few operands for its call-site type",
                            self.func.name, node
                        )
                    });
                assert!(
                    matches!(
                        self.role(&operands[0]),
                        ValueRole::Function | ValueRole::Place(_)
                    ),
                    "MIR function `{}` node {}: callee must be a function or function place",
                    self.func.name,
                    node
                );
                for index in 1..visible_start {
                    evidence(index);
                }
                for (offset, argument) in ty.fn_ty.args.iter().enumerate() {
                    let index = visible_start + offset;
                    assert!(
                        self.role(&operands[index]).is_place_operand(),
                        "MIR function `{}` node {}: visible call operand {} must be a place",
                        self.func.name,
                        node,
                        index
                    );
                    self.verify_place_representation(
                        node,
                        index,
                        &operands[index],
                        MirType::Lowered(argument.ty),
                    );
                }
                let result = operands.last().unwrap();
                assert!(
                    self.role(result).is_place_operand(),
                    "MIR function `{}` node {}: the trailing call result operand must be a \
                     place",
                    self.func.name,
                    node
                );
                if ty.fn_ty.ret != Type::never() {
                    let expected = if ty.result_convention.returns_place() {
                        MirType::Pointer(Box::new(MirType::Lowered(ty.fn_ty.ret)))
                    } else {
                        MirType::Lowered(ty.fn_ty.ret)
                    };
                    self.verify_place_representation(node, operands.len() - 1, result, expected);
                }
            }
            OperationKind::Project { yielded, ty } => {
                assert_eq!(
                    ty.result_convention,
                    crate::types::r#type::CallResultConvention::YIELDED_ONCE,
                    "MIR function `{}` node {}: project requires a YieldedOnce call convention",
                    self.func.name,
                    node
                );
                // First-class subscript adaptation can connect distinct generic descriptors whose
                // equality was established by HIR inference but is not retained in MIR. Concrete
                // call sites remain independently verifiable.
                if yielded.is_constant() && ty.fn_ty.ret.is_constant() {
                    assert!(
                        MirType::Lowered(*yielded)
                            .representation_compatible(&MirType::Lowered(ty.fn_ty.ret), &self.env,),
                        "MIR function `{}` node {}: project yield type {} differs from its call-site return type {}",
                        self.func.name,
                        node,
                        yielded.format_with(&self.env),
                        ty.fn_ty.ret.format_with(&self.env)
                    );
                }
                let visible_start = operands
                    .len()
                    .checked_sub(ty.fn_ty.args.len())
                    .filter(|start| *start >= 1)
                    .unwrap_or_else(|| {
                        panic!(
                            "MIR function `{}` node {}: project has too few operands for its call-site type",
                            self.func.name, node
                        )
                    });
                assert!(
                    matches!(
                        self.role(&operands[0]),
                        ValueRole::Function | ValueRole::Place(_)
                    ),
                    "MIR function `{}` node {}: callee must be a function or function place",
                    self.func.name,
                    node
                );
                for index in 1..visible_start {
                    evidence(index);
                }
                for (offset, argument) in ty.fn_ty.args.iter().enumerate() {
                    let index = visible_start + offset;
                    place(index);
                    self.verify_place_representation(
                        node,
                        index,
                        &operands[index],
                        MirType::Lowered(argument.ty),
                    );
                }
            }
            OperationKind::EndProject => {
                assert!(
                    matches!(self.role(&operands[0]), ValueRole::OpenProjection { .. }),
                    "MIR function `{}` node {}: end_project requires an open projection",
                    self.func.name,
                    node
                );
            }
            OperationKind::ExtractTag
            | OperationKind::Clear
            | OperationKind::DropClosureEnv
            | OperationKind::CloneClosureEnv { .. } => place(0),
            OperationKind::CompareEqual => {
                assert!(
                    self.role(&operands[0]).is_place_operand()
                        || self.materialized_type(&operands[0]).is_some(),
                    "MIR function `{}` node {}: comparison scrutinee must be a place or value",
                    self.func.name,
                    node
                );
                assert!(
                    matches!(self.role(&operands[1]), ValueRole::Pattern),
                    "MIR function `{}` node {}: comparison pattern must be compile-time data",
                    self.func.name,
                    node
                );
            }
            OperationKind::Load => place(0),
            OperationKind::Subfield { .. } => {
                place(0);
                value(1);
            }
            OperationKind::DictEntry { .. } => evidence(0),
            OperationKind::SubscriptMember { .. } => evidence(0),
            OperationKind::BuildSubscript { .. } => {
                for index in 0..operands.len() {
                    evidence(index);
                }
            }
            OperationKind::Store => {
                assert!(
                    self.materialized_type(&operands[0]).is_some()
                        || self.role(&operands[0]).is_place_operand()
                        || self.role(&operands[0]).is_materialized(),
                    "MIR function `{}` node {}: stored operand must be a value or place pointer",
                    self.func.name,
                    node
                );
                place(1);
                if let (Some(value_ty), Some(destination_ty)) = (
                    self.materialized_type(&operands[0]),
                    self.place_pointee_type(&operands[1]),
                ) {
                    assert!(
                        value_ty.representation_compatible(&destination_ty, &self.env),
                        "MIR function `{}` node {}: stored value type {} differs from \
                         destination type {}\n{}",
                        self.func.name,
                        node,
                        value_ty.format(&self.env),
                        destination_ty.format(&self.env),
                        self.func.format_with(&self.env)
                    );
                }
            }
            OperationKind::Memcpy | OperationKind::Move => {
                place(0);
                place(1);
                if let (Some(source_ty), Some(destination_ty)) = (
                    self.place_pointee_type(&operands[0]),
                    self.place_pointee_type(&operands[1]),
                ) {
                    // A witnessed dynamic move may connect distinct generic descriptors whose
                    // equality was established by HIR inference but is not retained in the lowered
                    // MIR signature. The witness supplies the runtime layout; making this check
                    // fully standalone requires explicit normalized-layout/equality metadata.
                    assert!(
                        operands.len() == 3
                            || source_ty.representation_compatible(&destination_ty, &self.env),
                        "MIR function `{}` node {}: source pointee type {} differs from \
                         destination pointee type {}\n{}",
                        self.func.name,
                        node,
                        source_ty.format(&self.env),
                        destination_ty.format(&self.env),
                        self.func.format_with(&self.env)
                    );
                }
                if operands.len() == 3 {
                    evidence(2);
                }
            }
            OperationKind::StackRestore => assert!(
                matches!(self.role(&operands[0]), ValueRole::StackMarker),
                "MIR function `{}` node {}: stack_restore needs a stack marker",
                self.func.name,
                node
            ),
            OperationKind::Drop => {
                place(0);
                assert!(
                    matches!(
                        self.role(&operands[1]),
                        ValueRole::Function | ValueRole::Place(_)
                    ),
                    "MIR function `{}` node {}: drop callee must be a function or function place",
                    self.func.name,
                    node
                );
            }
            OperationKind::BuildClosure {
                num_hidden_dicts,
                has_env_dict,
                ..
            } => {
                for index in 0..*num_hidden_dicts as usize {
                    evidence(index);
                }
                let captures_end = operands.len() - usize::from(*has_env_dict);
                for index in *num_hidden_dicts as usize..captures_end {
                    place(index);
                }
                if *has_env_dict {
                    evidence(operands.len() - 1);
                }
            }
        }
    }

    fn operation_is_source_fallible(&self, operation: &Operation) -> bool {
        match operation.source_fallibility() {
            SourceFallibility::Infallible => false,
            SourceFallibility::Fallible => true,
            SourceFallibility::FromOpenProjection => match self.role(&operation.operands[0]) {
                ValueRole::OpenProjection { accessor, .. } => call_type_is_fallible(&accessor),
                _ => false,
            },
        }
    }

    fn compute_instruction_dominance(&self) -> NodeDominance {
        let node_count = self.node_order.len();
        let entry = self.node_index[&self.block_first[&self.func.entry()]];
        let mut successors = vec![Vec::new(); node_count];
        let mut predecessors = vec![Vec::new(); node_count];
        for (node_index, &node) in self.node_order.iter().enumerate() {
            for (successor, _) in self.successors(node) {
                let successor = self.node_index[&successor];
                if !successors[node_index].contains(&successor) {
                    successors[node_index].push(successor);
                    predecessors[successor].push(node_index);
                }
            }
        }

        // Compute reverse postorder without recursion so verifier capacity is independent of the
        // host thread's call-stack size.
        let mut visited = vec![false; node_count];
        let mut postorder = Vec::new();
        let mut stack = vec![(entry, 0)];
        visited[entry] = true;
        while let Some((node, next_successor)) = stack.last_mut() {
            if let Some(&successor) = successors[*node].get(*next_successor) {
                *next_successor += 1;
                if !visited[successor] {
                    visited[successor] = true;
                    stack.push((successor, 0));
                }
            } else {
                postorder.push(*node);
                stack.pop();
            }
        }
        postorder.reverse();
        let reverse_postorder = postorder;
        let mut reverse_postorder_index = vec![NodeDominance::UNREACHABLE; node_count];
        for (index, &node) in reverse_postorder.iter().enumerate() {
            reverse_postorder_index[node] = index;
        }

        // Dominance is defined over operations and terminators. In particular, an invoked
        // operation's result is anchored at its normal successor and cannot dominate its error
        // successor.
        let mut immediate_dominator = vec![None; node_count];
        immediate_dominator[entry] = Some(entry);
        loop {
            let mut changed = false;
            for &node in reverse_postorder.iter().skip(1) {
                let mut known_predecessors = predecessors[node]
                    .iter()
                    .copied()
                    .filter(|&predecessor| immediate_dominator[predecessor].is_some());
                let mut new_dominator = known_predecessors
                    .next()
                    .expect("a reachable non-entry node must have a known predecessor");
                for predecessor in known_predecessors {
                    new_dominator = intersect_dominator_paths(
                        predecessor,
                        new_dominator,
                        &immediate_dominator,
                        &reverse_postorder_index,
                    );
                }
                if immediate_dominator[node] != Some(new_dominator) {
                    immediate_dominator[node] = Some(new_dominator);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }

        let mut dominator_tree = vec![Vec::new(); node_count];
        for &node in reverse_postorder.iter().skip(1) {
            let dominator = immediate_dominator[node]
                .expect("every reachable node must have an immediate dominator");
            dominator_tree[dominator].push(node);
        }

        let mut preorder = vec![NodeDominance::UNREACHABLE; node_count];
        let mut postorder = vec![NodeDominance::UNREACHABLE; node_count];
        let mut timestamp = 0;
        let mut stack = vec![(entry, false)];
        while let Some((node, exiting)) = stack.pop() {
            if exiting {
                postorder[node] = timestamp;
                timestamp += 1;
                continue;
            }
            preorder[node] = timestamp;
            timestamp += 1;
            stack.push((node, true));
            for &child in dominator_tree[node].iter().rev() {
                stack.push((child, false));
            }
        }

        NodeDominance {
            preorder,
            postorder,
        }
    }

    fn place_pointee_type(&self, value: &mir::Value) -> Option<MirType> {
        match self.role(value) {
            ValueRole::Place(ty) => Some(ty),
            ValueRole::Materialized(MirType::Pointer(ty)) => Some(*ty),
            ValueRole::OpenProjection { yielded, .. } => Some(MirType::Lowered(yielded)),
            _ => None,
        }
    }

    /// Checks that a call's recorded instantiation actually explains its call-site type.
    ///
    /// Substituting the callee's declared signature by the recorded arguments must reproduce the
    /// concrete signature the call site carries. This is the invariant that makes the instantiation
    /// trustworthy: it is recorded during inference and consumed much later by specialization, and
    /// nothing in between would otherwise notice if the two drifted apart.
    ///
    /// Only checked for a statically known callee — an indirect call has no declared signature to
    /// substitute — and only when an instantiation was recorded. A generic callee with none is not
    /// an error here: some call sites are synthesized by the compiler rather than lowered from a
    /// generic application.
    fn verify_instantiation(
        &self,
        node: usize,
        callee: &mir::Value,
        ty: &CallImplType,
        instantiation: Option<&mir::Instantiation>,
    ) {
        let (Some(instantiation), mir::Value::Function(callee)) = (instantiation, callee) else {
            return;
        };
        let Some(module) = self.env.module_by_id(callee.module) else {
            return;
        };
        let Some(function) = module.get_function_by_id(callee.function) else {
            return;
        };
        let scheme = &function.definition.ty_scheme;
        assert_eq!(
            instantiation.ty_args.len(),
            scheme.ty_quantifiers.len(),
            "MIR function `{}` node {}: call records {} type arguments for a callee with {} type \
             quantifiers",
            self.func.name,
            node,
            instantiation.ty_args.len(),
            scheme.ty_quantifiers.len()
        );

        // The same substitution monomorphization applies to the callee's body, so the two cannot
        // disagree about what the recorded arguments mean.
        let subst = instantiation.substitution(scheme);
        let substituted = scheme.ty.instantiate_simple(&subst);
        assert_eq!(
            substituted.args.len(),
            ty.fn_ty.args.len(),
            "MIR function `{}` node {}: instantiating the callee's signature gives {} arguments \
             but the call site's type has {}",
            self.func.name,
            node,
            substituted.args.len(),
            ty.fn_ty.args.len()
        );
        // Rendered rather than compared by handle: a mismatch here is a lowering bug, and the two
        // types are what identifies it.
        assert!(
            substituted.ret == ty.fn_ty.ret,
            "MIR function `{}` node {}: instantiating {}'s signature by the recorded arguments \
             [{}] gives return type {}, but the call site's type says {}",
            self.func.name,
            node,
            mir::Value::Function(*callee).format_with(&self.env),
            instantiation
                .ty_args
                .iter()
                .map(|ty| ty.format_with(&self.env).to_string())
                .collect::<Vec<_>>()
                .join(", "),
            substituted.ret.format_with(&self.env),
            ty.fn_ty.ret.format_with(&self.env),
        );
    }

    fn verify_place_representation(
        &self,
        node: NodeId,
        operand_index: usize,
        value: &mir::Value,
        expected: MirType,
    ) {
        let actual = self.place_pointee_type(value).unwrap_or_else(|| {
            panic!(
                "MIR function `{}` node {}: operand {} has no place representation",
                self.func.name, node, operand_index
            )
        });
        // Generic descriptor equalities are established by HIR inference but are not yet retained
        // as standalone MIR witnesses. Check every independently concrete representation here;
        // explicit normalized-layout/equality metadata can close the remaining generic boundary.
        if !actual.is_fully_concrete() || !expected.is_fully_concrete() {
            return;
        }
        assert!(
            actual.representation_compatible(&expected, &self.env),
            "MIR function `{}` node {}: operand {} place representation {} differs from expected {}\n{}",
            self.func.name,
            node,
            operand_index,
            actual.format(&self.env),
            expected.format(&self.env),
            self.func.format_with(&self.env)
        );
    }

    fn verify_register_consumption(&mut self) {
        let mut consuming_uses: FxHashMap<mir::Value, usize> = FxHashMap::default();
        for &node in &self.node_order {
            let Some(whole) = self.operation(node) else {
                continue;
            };
            for (index, operand) in whole.operands.iter().enumerate() {
                if self.operand_consumes_value(whole, index) {
                    *consuming_uses.entry(operand.clone()).or_default() += 1;
                }
            }
        }
        for &node in &self.node_order {
            let Some(value) = self.definition(node) else {
                continue;
            };
            if self.register_needs_consuming_use(node) {
                assert_eq!(
                    consuming_uses.get(&value).copied().unwrap_or(0),
                    1,
                    "MIR function `{}`: owned register {value} must have exactly one consuming use",
                    self.func.name
                );
            }
        }
    }

    fn operand_consumes_value(&self, node: &crate::mir::Operation, index: usize) -> bool {
        matches!(node.kind, OperationKind::Store) && index == 0
    }

    fn register_needs_consuming_use(&self, node: NodeId) -> bool {
        let Some(operation) = self.operation(node) else {
            return false;
        };
        match &operation.kind {
            OperationKind::Variant { .. } | OperationKind::CloneClosureEnv { .. } => true,
            OperationKind::BuildClosure {
                num_hidden_dicts,
                has_env_dict,
                ..
            } => {
                let captures = operation.operands.len()
                    - *num_hidden_dicts as usize
                    - usize::from(*has_env_dict);
                captures != 0
            }
            _ => false,
        }
    }

    fn verify_storage_ownership(&mut self) {
        let initial_roots = self
            .roots
            .iter()
            .map(|root| {
                StorageState::shaped(root.ty, LeafState::UNALLOCATED, &self.env, &mut Vec::new())
            })
            .collect();
        let initial = AnalysisState {
            roots: initial_roots,
            markers: FxHashMap::default(),
            open_projections: FxHashSet::default(),
        };
        // Keep different allocation frontiers and stack-marker snapshots as separate alternatives.
        // Merging either correlation would make it impossible to verify what a later
        // `stack_restore` reclaims. Within one alternative, ordinary ownership states still join to
        // a fixed point.
        let mut inputs: Vec<Vec<AnalysisState>> = vec![vec![]; self.node_order.len()];
        let entry = self.block_first[&self.func.entry()];
        inputs[self.node_index[&entry]].push(initial);
        let mut worklist = VecDeque::from([(entry, 0)]);

        while let Some((node, alternative)) = worklist.pop_front() {
            let index = self.node_index[&node];
            let input = inputs[index][alternative].clone();
            let edges = self.transfer(node, &input);
            for (target, state) in edges {
                let target_index = self.node_index[&target];
                let alternatives = &mut inputs[target_index];
                let (alternative, changed) = match alternatives.iter().position(|existing| {
                    existing.markers == state.markers
                        && existing.open_projections == state.open_projections
                        && existing.has_same_allocation_frontier(&state)
                }) {
                    Some(alternative) => {
                        let changed =
                            alternatives[alternative].join_roots(&state, self.func, &self.env);
                        (alternative, changed)
                    }
                    None => {
                        let alternative = alternatives.len();
                        alternatives.push(state);
                        (alternative, true)
                    }
                };
                if changed {
                    worklist.push_back((target, alternative));
                }
            }
        }
    }

    fn transfer(&mut self, node: NodeId, input: &AnalysisState) -> Vec<(NodeId, AnalysisState)> {
        let mut normal = input.clone();
        let mut unwind = input.clone();

        if let Some(whole) = self.operation(node) {
            // Keep no borrow of `self.func` while the transfer mutates verifier caches.
            let kind = whole.kind.clone();
            let operands = whole.operands.clone();
            match &kind {
                OperationKind::Alloca { .. } => {
                    let root = self.root_index[&self.definition(node).unwrap()];
                    normal.roots[root].set_all(LeafState::ABSENT);
                }
                OperationKind::AllocaPlace { .. } => {}
                OperationKind::Store => {
                    self.transfer_store(&operands[0], &operands[1], &mut normal);
                }
                OperationKind::Memcpy => {
                    if let Some(MirType::Lowered(ty)) = self.place_pointee_type(&operands[0]) {
                        assert!(
                            self.is_trivial_copy(ty),
                            "MIR function `{}`: memcpy source type is not TrivialCopy",
                            self.func.name
                        );
                    }
                    self.transfer_copy_or_move(&operands[0], &operands[1], false, &mut normal);
                }
                OperationKind::Move => {
                    self.transfer_copy_or_move(&operands[0], &operands[1], true, &mut normal);
                }
                OperationKind::Clear => {
                    self.transfer_clear(&operands[0], &mut normal);
                }
                OperationKind::Drop => {
                    self.transfer_drop(&operands[0], &mut normal);
                    self.transfer_drop(&operands[0], &mut unwind);
                }
                OperationKind::Call { .. } => {
                    // Operation arity and role verification establish that every call ends in a
                    // result place, including calls returning unit.
                    let destination = operands
                        .last()
                        .expect("call arity was verified before ownership analysis");
                    self.initialize_call_result(node, destination, &mut normal);
                }
                OperationKind::BuildClosure {
                    num_hidden_dicts,
                    has_env_dict,
                    ..
                } => {
                    let captures_end = operands.len() - usize::from(*has_env_dict);
                    for capture in &operands[*num_hidden_dicts as usize..captures_end] {
                        self.consume_place(capture, &mut normal);
                    }
                }
                OperationKind::StackSave => {
                    let marker = self.definition(node).unwrap();
                    for (index, root) in normal.roots.iter().enumerate() {
                        debug_assert!(
                            root.state.is_definitely_unallocated()
                                || !root.state.may_be_unallocated(),
                            "MIR function `{}` node {}: allocation-frontier alternatives were \
                         incorrectly merged before stack_save for {}",
                            self.func.name,
                            node,
                            self.roots[index].value
                        );
                    }
                    let snapshot = normal
                        .roots
                        .iter()
                        .map(|root| !root.state.may_be_unallocated())
                        .collect();
                    normal.markers.insert(marker, snapshot);
                }
                OperationKind::StackRestore => {
                    self.transfer_stack_restore(&operands[0], &mut normal);
                }
                OperationKind::Project { .. } => {
                    let projection = self.definition(node).unwrap();
                    assert!(normal.open_projections.insert(projection));
                }
                OperationKind::EndProject => {
                    let projection = &operands[0];
                    assert!(
                        normal.open_projections.remove(projection),
                        "MIR function `{}` node {}: end_project consumes an inactive projection",
                        self.func.name,
                        node
                    );
                    // The projection lifetime ends when the slide starts, even if the slide raises.
                    assert!(unwind.open_projections.remove(projection));
                }
                _ => {}
            }
        }

        match self.terminator(node) {
            Some(TerminatorKind::Return | TerminatorKind::PropagateError) => {
                self.verify_frame_exit(node, input);
            }
            Some(TerminatorKind::FailureDuringCleanup) => {
                // Poisoning transfers remaining ownership to runtime reclamation.
            }
            _ => {}
        }

        let mut result = vec![];
        for (target, edge) in self.successors(node) {
            result.push((
                target,
                match edge {
                    EdgeKind::Normal => normal.clone(),
                    EdgeKind::Error => unwind.clone(),
                },
            ));
        }
        result
    }

    fn transfer_store(
        &mut self,
        value: &mir::Value,
        destination: &mir::Value,
        state: &mut AnalysisState,
    ) {
        let LocalPlace::Root { root, path } = self.local_place(destination) else {
            return;
        };
        let Some(path) = path else {
            return;
        };
        let Some(target) = state.roots[root].at_path(&path) else {
            self.mark_opaque_projection_live(root, &path, state);
            return;
        };
        assert!(
            target.state.may_be_overwritten_without_drop(),
            "MIR function `{}`: store overwrites storage with a live semantic drop obligation",
            self.func.name
        );
        let needs_drop = self.value_needs_drop(value);
        let live = if needs_drop {
            self.live_state_for_type(target.ty)
        } else {
            StorageState::shaped(
                target.ty,
                LeafState::LIVE_NO_DROP,
                &self.env,
                &mut Vec::new(),
            )
        };
        state.roots[root].replace_path(&path, &live);
    }

    fn transfer_copy_or_move(
        &mut self,
        source: &mir::Value,
        destination: &mir::Value,
        is_move: bool,
        state: &mut AnalysisState,
    ) {
        let source_place = self.local_place(source);
        let destination_place = self.local_place(destination);
        let source_value = match &source_place {
            LocalPlace::Root {
                root,
                path: Some(path),
            } => state.roots[*root].at_path(path).map(|source_state| {
                assert!(
                    source_state.state.is_definitely_live(),
                    "MIR function `{}`: {} reads storage that is not definitely initialized \
                         ({source_state:?}, operand {source})\n{}",
                    self.func.name,
                    if is_move { "move" } else { "memcpy" },
                    self.func.format_with(&self.env)
                );
                source_state.clone()
            }),
            _ => None,
        };

        if let LocalPlace::Root {
            root,
            path: Some(path),
        } = destination_place
        {
            if let Some(target) = state.roots[root].at_path(&path) {
                assert!(
                    target.state.may_be_overwritten_without_drop(),
                    "MIR function `{}`: {} overwrites storage with a live semantic drop obligation",
                    self.func.name,
                    if is_move { "move" } else { "memcpy" }
                );
                let replacement = match source_value {
                    Some(source) if source.ty == target.ty => source,
                    _ if is_move => self.live_state_for_type(target.ty),
                    _ => StorageState::shaped(
                        target.ty,
                        LeafState::LIVE_NO_DROP,
                        &self.env,
                        &mut Vec::new(),
                    ),
                };
                state.roots[root].replace_path(&path, &replacement);
            } else {
                self.mark_opaque_projection_live(root, &path, state);
            }
        }

        if is_move
            && let LocalPlace::Root {
                root,
                path: Some(path),
            } = source_place
        {
            state.roots[root].set_path_all(&path, LeafState::ABSENT);
        }
    }

    fn transfer_clear(&self, destination: &mir::Value, state: &mut AnalysisState) {
        let LocalPlace::Root {
            root,
            path: Some(path),
        } = self.local_place(destination)
        else {
            return;
        };
        let Some(target) = state.roots[root].at_path(&path) else {
            // The projection is inside an opaque shell — a variant payload, a native interior —
            // which retains its ownership as a whole. Clearing a subplace of one cannot be
            // represented, and must not erase the shell's obligation, so the state is left alone;
            // `transfer_store` gives up on the same paths for the same reason. Emitted MIR clears
            // such a place only through a parameter, which is not a tracked root at all, but
            // inlining rebases a callee's parameter onto the caller's `alloca`.
            return;
        };
        assert!(
            target.state.may_be_overwritten_without_drop(),
            "MIR function `{}`: clear discards a live semantic drop obligation",
            self.func.name
        );
        state.roots[root].set_path_all(&path, LeafState::ABSENT);
    }

    fn transfer_drop(&self, target: &mir::Value, state: &mut AnalysisState) {
        let LocalPlace::Root {
            root,
            path: Some(path),
        } = self.local_place(target)
        else {
            return;
        };
        assert!(
            !state.roots[root]
                .at_path(&path)
                .expect("tracked drop path must exist")
                .state
                .may_be_unallocated(),
            "MIR function `{}`: drop targets storage that may not have been allocated",
            self.func.name
        );
        state.roots[root].set_path_all(&path, LeafState::ABSENT);
    }

    fn consume_place(&self, source: &mir::Value, state: &mut AnalysisState) {
        let LocalPlace::Root {
            root,
            path: Some(path),
        } = self.local_place(source)
        else {
            return;
        };
        let source_state = state.roots[root]
            .at_path(&path)
            .expect("tracked capture path must exist")
            .state;
        assert!(
            source_state.is_definitely_live(),
            "MIR function `{}`: closure capture consumes storage that is not definitely initialized",
            self.func.name
        );
        state.roots[root].set_path_all(&path, LeafState::ABSENT);
    }

    fn initialize_call_result(
        &mut self,
        node: NodeId,
        destination: &mir::Value,
        state: &mut AnalysisState,
    ) {
        let LocalPlace::Root {
            root,
            path: Some(path),
        } = self.local_place(destination)
        else {
            return;
        };
        let Some(target) = state.roots[root].at_path(&path) else {
            self.mark_opaque_projection_live(root, &path, state);
            return;
        };
        assert!(
            target.state.may_be_overwritten_without_drop(),
            "MIR function `{}` node {}: call result overwrites storage with a live semantic \
             drop obligation in {destination} ({target:?})\n{}",
            self.func.name,
            node,
            self.func.format_with(&self.env)
        );
        let live = self.live_state_for_type(target.ty);
        state.roots[root].replace_path(&path, &live);
    }

    fn mark_opaque_projection_live(
        &mut self,
        root: usize,
        path: &[usize],
        state: &mut AnalysisState,
    ) {
        let prefix_len = state.roots[root].tracked_prefix_len(path);
        debug_assert!(prefix_len < path.len());
        let prefix = &path[..prefix_len];
        let ancestor_ty = state.roots[root]
            .at_path(prefix)
            .expect("tracked opaque projection prefix must exist")
            .ty;
        let live = self.live_state_for_type(ancestor_ty);
        state.roots[root].replace_path(prefix, &live);
    }

    fn transfer_stack_restore(&self, marker: &mir::Value, state: &mut AnalysisState) {
        // A stack marker is an immutable saved frontier, not a linear value. Lowering may restore
        // the same marker repeatedly after allocating new temporaries at that frontier.
        let snapshot = state.markers.get(marker).cloned().unwrap_or_else(|| {
            panic!(
                "MIR function `{}`: stack_restore uses a marker unavailable on this path",
                self.func.name
            )
        });
        for (index, was_live) in snapshot.into_iter().enumerate() {
            if was_live {
                continue;
            }
            let root = &mut state.roots[index];
            assert!(
                !root.state.may_need_drop(),
                "MIR function `{}`: stack_restore reclaims storage with a live semantic drop \
                 obligation in {} ({root:?})\n{}",
                self.func.name,
                self.roots[index].value,
                self.func.format_with(&self.env)
            );
            root.set_all(LeafState::UNALLOCATED);
        }
    }

    fn verify_frame_exit(&self, node: NodeId, state: &AnalysisState) {
        assert!(
            state.open_projections.is_empty(),
            "MIR function `{}` node {}: frame exits with an open projection",
            self.func.name,
            node
        );
        for (index, root) in state.roots.iter().enumerate() {
            if !self.roots[index].exact {
                continue;
            }
            assert!(
                !root.state.may_need_drop(),
                "MIR function `{}` node {}: frame exits with a live semantic drop \
                 obligation in {}",
                self.func.name,
                node,
                self.roots[index].value
            );
        }
    }

    fn storage_paths_are_exact(&mut self, ty: Type, active: &mut Vec<Type>) -> bool {
        if self.is_trivial_copy(ty) {
            return true;
        }
        if active.contains(&ty) {
            return false;
        }
        active.push(ty);
        let kind = cloned_type_kind(ty);
        let result = match kind {
            TypeKind::Tuple(fields) => fields
                .into_iter()
                .all(|field| self.storage_paths_are_exact(field, active)),
            TypeKind::Record(fields) => fields
                .into_iter()
                .all(|(_, field)| self.storage_paths_are_exact(field, active)),
            TypeKind::Named(named) if !self.env.type_def(named.def).has_custom_value_impl => {
                let def = self.env.type_def(named.def);
                let shape =
                    def.instantiated_shape_with_effects(&named.params, &named.effect_params);
                self.storage_paths_are_exact(shape, active)
            }
            _ => false,
        };
        active.pop();
        result
    }

    fn value_needs_drop(&mut self, value: &mir::Value) -> bool {
        match value {
            mir::Value::Constant(_)
            | mir::Value::Function(_)
            | mir::Value::Subscript(_)
            | mir::Value::Dictionary(_)
            | mir::Value::Pattern(_) => false,
            mir::Value::Parameter(_) => false,
            mir::Value::Register(value_id) => {
                let node = self.value_definition[value_id];
                let operation = self.operation(node).unwrap();
                match &operation.kind {
                    OperationKind::Variant { .. } | OperationKind::CloneClosureEnv { .. } => true,
                    OperationKind::BuildClosure {
                        num_hidden_dicts,
                        has_env_dict,
                        ..
                    } => {
                        operation.operands.len()
                            > *num_hidden_dicts as usize + usize::from(*has_env_dict)
                    }
                    OperationKind::Load
                    | OperationKind::CompareEqual
                    | OperationKind::ExtractTag
                    | OperationKind::BuildSubscript { .. } => false,
                    _ => match operation.result() {
                        OperationResult::Lowered(ty) => !self.is_trivial_copy(ty),
                        _ => false,
                    },
                }
            }
        }
    }

    fn live_state_for_type(&mut self, ty: Type) -> StorageState {
        if ty == Type::never() {
            // A `never` destination exists only to keep the uniform out-pointer call shape. Its
            // call cannot produce a runtime value on the normal edge, so it carries no semantic
            // drop obligation even when the CFG retains a syntactic normal successor.
            return StorageState::shaped(ty, LeafState::LIVE_NO_DROP, &self.env, &mut Vec::new());
        }
        if self.is_trivial_copy(ty) {
            return StorageState::shaped(ty, LeafState::LIVE_NO_DROP, &self.env, &mut Vec::new());
        }
        match cloned_type_kind(ty) {
            TypeKind::Tuple(_) | TypeKind::Record(_) => {
                let mut result =
                    StorageState::shaped(ty, LeafState::LIVE_NO_DROP, &self.env, &mut Vec::new());
                for field in &mut result.fields {
                    *field = self.live_state_for_type(field.ty);
                }
                result.recompute();
                result
            }
            TypeKind::Named(named) if !self.env.type_def(named.def).has_custom_value_impl => {
                let mut result =
                    StorageState::shaped(ty, LeafState::LIVE_NO_DROP, &self.env, &mut Vec::new());
                if result.fields.is_empty() {
                    result.set_all(LeafState::LIVE_NEEDS_DROP);
                } else {
                    for field in &mut result.fields {
                        *field = self.live_state_for_type(field.ty);
                    }
                    result.recompute();
                }
                result
            }
            _ => StorageState::shaped(ty, LeafState::LIVE_NEEDS_DROP, &self.env, &mut Vec::new()),
        }
    }

    fn is_trivial_copy(&mut self, ty: Type) -> bool {
        if let Some(result) = self.trivial_copy.get(&ty) {
            return *result;
        }
        let result = self.solver.concrete_type_is_trivial_copy(ty);
        self.trivial_copy.insert(ty, result);
        result
    }

    fn local_place(&self, value: &mir::Value) -> LocalPlace {
        let mir::Value::Register(value_id) = value else {
            return LocalPlace::External;
        };
        let node = self.value_definition[value_id];
        let operation = self.operation(node).unwrap();
        match &operation.kind {
            OperationKind::Alloca { .. } => LocalPlace::Root {
                root: self.root_index[value],
                path: Some(vec![]),
            },
            OperationKind::Subfield { .. } => {
                let base = self.local_place(&operation.operands[0]);
                let index = self.static_field_index(&operation.operands[1]);
                match base {
                    LocalPlace::Root { root, path } => LocalPlace::Root {
                        root,
                        path: path.and_then(|mut path| {
                            path.push(index?);
                            Some(path)
                        }),
                    },
                    LocalPlace::External => LocalPlace::External,
                }
            }
            _ => LocalPlace::External,
        }
    }

    fn static_field_index(&self, value: &mir::Value) -> Option<usize> {
        let mir::Value::Constant(id) = value else {
            return None;
        };
        self.func
            .constant(*id)
            .representation
            .as_primitive_ty::<isize>()
            .and_then(|index| usize::try_from(*index).ok())
    }

    fn successors(&self, node: NodeId) -> Vec<(NodeId, EdgeKind)> {
        let mut result = vec![];
        let first = |block: &BlockId| self.block_first[block];
        match self.terminator(node) {
            Some(TerminatorKind::CondBr {
                then_target,
                else_target,
                ..
            }) => {
                result.push((first(then_target), EdgeKind::Normal));
                result.push((first(else_target), EdgeKind::Normal));
            }
            Some(TerminatorKind::Goto { target }) => {
                result.push((first(target), EdgeKind::Normal));
            }
            Some(TerminatorKind::Invoke { normal, error, .. }) => {
                result.push((first(normal), EdgeKind::Normal));
                result.push((first(error), EdgeKind::Error));
            }
            Some(TerminatorKind::Yield { resume, .. }) => {
                // Suspension is not a function exit: `EndProject` resumes at this explicit block.
                result.push((first(resume), EdgeKind::Normal));
            }
            Some(
                TerminatorKind::Return
                | TerminatorKind::PropagateError
                | TerminatorKind::FailureDuringCleanup,
            ) => {}
            None => {
                let index = self.node_index[&node];
                let next = self
                    .node_order
                    .get(index + 1)
                    .copied()
                    .filter(|next| self.node_block[next] == self.node_block[&node]);
                if let Some(next) = next {
                    result.push((next, EdgeKind::Normal));
                }
            }
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        CompilerSession, Location,
        hir::value::LiteralValue,
        mir::{
            BlockId, Operation, ParameterKind, Value, builder::FunctionBuilder,
            terminator::Terminator,
        },
        module::{FunctionId, LocalFunctionId, ModuleId},
        std::math::int_type,
        types::{
            effects::{PrimitiveEffect, effect, no_effects},
            r#type::{CallImplType, CallResultConvention, FnType, Type},
        },
    };

    fn verify(f: FunctionBuilder) {
        let session = CompilerSession::new();
        f.finish(session.module_env());
    }

    fn append_result(f: &mut FunctionBuilder, block: BlockId, operation: Operation) -> Value {
        f.append_operation(block, operation)
            .expect("test node should define a value")
    }

    fn append(f: &mut FunctionBuilder, block: BlockId, operation: Operation) {
        f.append_operation(block, operation);
    }

    fn terminate_return(f: &mut FunctionBuilder, block: BlockId, span: Location) {
        f.set_terminator(block, Terminator::ret(span));
    }

    fn managed_variant_ty() -> Type {
        Type::variant([(ustr::ustr("A"), Type::unit())])
    }

    #[test]
    #[should_panic(expected = "store overwrites storage with a live semantic drop obligation")]
    fn rejects_overwriting_owned_storage_without_drop() {
        let span = Location::new_synthesized();
        let session = CompilerSession::new();
        let env = session.module_env();
        let mut f = FunctionBuilder::new("bad_store".into(), Default::default());
        let ret = f.add_parameter(int_type(), ParameterKind::Return);
        let constant = f.add_constant(int_type(), LiteralValue::new_native(0isize), &env);
        let variant_ty = managed_variant_ty();
        let block = f.add_block();
        let local = append_result(&mut f, block, Operation::alloca(span, variant_ty));
        let first = append_result(
            &mut f,
            block,
            Operation::variant(span, ustr::ustr("A"), variant_ty),
        );
        append(&mut f, block, Operation::store(span, first, local.clone()));
        let second = append_result(
            &mut f,
            block,
            Operation::variant(span, ustr::ustr("A"), variant_ty),
        );
        append(&mut f, block, Operation::store(span, second, local));
        append(
            &mut f,
            block,
            Operation::store(
                span,
                crate::mir::Value::Constant(constant),
                crate::mir::Value::Parameter(ret),
            ),
        );
        terminate_return(&mut f, block, span);
        verify(f);
    }

    #[test]
    #[should_panic(expected = "does not dominate")]
    fn rejects_register_use_not_dominated_by_its_definition() {
        let span = Location::new_synthesized();
        let session = CompilerSession::new();
        let env = session.module_env();
        let mut f = FunctionBuilder::new("bad_dominance".into(), Default::default());
        let condition = f.add_constant(
            crate::std::logic::bool_type(),
            LiteralValue::new_native(true),
            &env,
        );
        let variant_ty = managed_variant_ty();
        let entry = f.add_block();
        let defining = f.add_block();
        let using = f.add_block();
        let local = append_result(&mut f, entry, Operation::alloca(span, variant_ty));
        f.set_terminator(
            entry,
            Terminator::cond_br(
                span,
                crate::mir::Value::Constant(condition),
                defining,
                using,
            ),
        );
        let value = append_result(
            &mut f,
            defining,
            Operation::variant(span, ustr::ustr("A"), variant_ty),
        );
        f.set_terminator(defining, Terminator::goto(span, using));
        append(&mut f, using, Operation::store(span, value, local));
        terminate_return(&mut f, using, span);
        verify(f);
    }

    #[test]
    fn accepts_entry_definition_used_after_a_diamond() {
        let span = Location::new_synthesized();
        let session = CompilerSession::new();
        let env = session.module_env();
        let mut f = FunctionBuilder::new("diamond_dominance".into(), Default::default());
        let condition = f.add_constant(
            crate::std::logic::bool_type(),
            LiteralValue::new_native(true),
            &env,
        );
        let value = f.add_constant(int_type(), LiteralValue::new_native(42isize), &env);
        let ret = f.add_parameter(int_type(), ParameterKind::Return);
        let entry = f.add_block();
        let left = f.add_block();
        let right = f.add_block();
        let join = f.add_block();

        let local = append_result(&mut f, entry, Operation::alloca(span, int_type()));
        append(
            &mut f,
            entry,
            Operation::store(span, crate::mir::Value::Constant(value), local.clone()),
        );
        f.set_terminator(
            entry,
            Terminator::cond_br(span, crate::mir::Value::Constant(condition), left, right),
        );
        f.set_terminator(left, Terminator::goto(span, join));
        f.set_terminator(right, Terminator::goto(span, join));
        let loaded = append_result(&mut f, join, Operation::load(span, local));
        append(
            &mut f,
            join,
            Operation::store(span, loaded, crate::mir::Value::Parameter(ret)),
        );
        terminate_return(&mut f, join, span);

        verify(f);
    }

    #[test]
    fn accepts_entry_definition_used_inside_and_after_a_loop() {
        let span = Location::new_synthesized();
        let session = CompilerSession::new();
        let env = session.module_env();
        let mut f = FunctionBuilder::new("loop_dominance".into(), Default::default());
        let condition = f.add_constant(
            crate::std::logic::bool_type(),
            LiteralValue::new_native(true),
            &env,
        );
        let value = f.add_constant(int_type(), LiteralValue::new_native(42isize), &env);
        let ret = f.add_parameter(int_type(), ParameterKind::Return);
        let entry = f.add_block();
        let header = f.add_block();
        let body = f.add_block();
        let exit = f.add_block();

        let local = append_result(&mut f, entry, Operation::alloca(span, int_type()));
        append(
            &mut f,
            entry,
            Operation::store(span, crate::mir::Value::Constant(value), local.clone()),
        );
        f.set_terminator(entry, Terminator::goto(span, header));
        append(&mut f, header, Operation::load(span, local.clone()));
        f.set_terminator(
            header,
            Terminator::cond_br(span, crate::mir::Value::Constant(condition), body, exit),
        );
        append(&mut f, body, Operation::load(span, local.clone()));
        f.set_terminator(body, Terminator::goto(span, header));
        let loaded = append_result(&mut f, exit, Operation::load(span, local));
        append(
            &mut f,
            exit,
            Operation::store(span, loaded, crate::mir::Value::Parameter(ret)),
        );
        terminate_return(&mut f, exit, span);

        verify(f);
    }

    #[test]
    #[should_panic(expected = "does not dominate")]
    fn rejects_invoke_result_used_on_its_error_edge() {
        let span = Location::new_synthesized();
        let mut f = FunctionBuilder::new("bad_unwind_dominance".into(), Default::default());
        let entry = f.add_block();
        let normal = f.add_block();
        let error = f.add_block();
        let callee = Value::Function(FunctionId::new(
            ModuleId::default(),
            LocalFunctionId::default(),
        ));
        let call_ty = CallImplType::new(
            FnType::new_by_val([], int_type(), effect(PrimitiveEffect::Fallible)),
            CallResultConvention::YIELDED_ONCE,
        );
        let projected = f
            .set_terminator(
                entry,
                Terminator::invoke(
                    span,
                    Operation::project(span, callee, [], int_type(), call_ty),
                    normal,
                    error,
                ),
            )
            .unwrap();
        terminate_return(&mut f, normal, span);
        append(&mut f, error, Operation::load(span, projected));
        f.set_terminator(error, Terminator::propagate_error(span));
        verify(f);
    }

    #[test]
    #[should_panic(expected = "trailing call result operand must be a place")]
    fn rejects_call_without_a_trailing_result_place() {
        let span = Location::new_synthesized();
        let mut f = FunctionBuilder::new("bad_call_result".into(), Default::default());
        let dictionary = f.add_parameter(int_type(), ParameterKind::Dictionary);
        let block = f.add_block();
        let callee = FunctionId {
            module: ModuleId::default(),
            function: LocalFunctionId::default(),
        };
        append(
            &mut f,
            block,
            Operation::call(
                span,
                crate::mir::Value::Function(callee),
                [crate::mir::Value::Parameter(dictionary)],
                CallImplType::value(FnType::new_by_val([], int_type(), no_effects())),
            ),
        );
        terminate_return(&mut f, block, span);
        verify(f);
    }

    #[test]
    #[should_panic(expected = "operand 1 place representation bool differs from expected int")]
    fn rejects_call_operand_incompatible_with_retained_call_type() {
        let span = Location::new_synthesized();
        let mut f = FunctionBuilder::new("bad_call_argument_type".into(), Default::default());
        let block = f.add_block();
        let argument = append_result(
            &mut f,
            block,
            Operation::alloca(span, crate::std::logic::bool_type()),
        );
        let result = append_result(&mut f, block, Operation::alloca(span, int_type()));
        append(
            &mut f,
            block,
            Operation::call(
                span,
                Value::Function(FunctionId::new(
                    ModuleId::default(),
                    LocalFunctionId::default(),
                )),
                [argument, result],
                CallImplType::value(FnType::new_by_val([int_type()], int_type(), no_effects())),
            ),
        );
        terminate_return(&mut f, block, span);
        verify(f);
    }

    #[test]
    #[should_panic(expected = "project yield type bool differs from its call-site return type int")]
    fn rejects_concrete_project_yield_incompatible_with_retained_call_type() {
        let span = Location::new_synthesized();
        let mut f = FunctionBuilder::new("bad_project_type".into(), Default::default());
        let block = f.add_block();
        append_result(
            &mut f,
            block,
            Operation::project(
                span,
                Value::Function(FunctionId::new(
                    ModuleId::default(),
                    LocalFunctionId::default(),
                )),
                [],
                crate::std::logic::bool_type(),
                CallImplType::new(
                    FnType::new_by_val([], int_type(), no_effects()),
                    CallResultConvention::YIELDED_ONCE,
                ),
            ),
        );
        terminate_return(&mut f, block, span);
        verify(f);
    }

    #[test]
    #[should_panic(expected = "propagate_error requires one in-flight source failure")]
    fn rejects_propagate_error_without_source_failure() {
        let span = Location::new_synthesized();
        let mut f = FunctionBuilder::new("bad_propagate".into(), Default::default());
        let block = f.add_block();
        f.set_terminator(block, Terminator::propagate_error(span));
        verify(f);
    }

    #[test]
    #[should_panic(expected = "return reached while a source failure is propagating")]
    fn rejects_source_error_edge_rejoining_normal_return() {
        let span = Location::new_synthesized();
        let mut f = FunctionBuilder::new("bad_error_return".into(), Default::default());
        let entry = f.add_block();
        let normal = f.add_block();
        let error = f.add_block();
        let result = append_result(&mut f, entry, Operation::alloca(span, int_type()));
        let call = Operation::call(
            span,
            Value::Function(FunctionId::new(
                ModuleId::default(),
                LocalFunctionId::default(),
            )),
            [result],
            CallImplType::value(FnType::new_by_val(
                [],
                int_type(),
                effect(PrimitiveEffect::Fallible),
            )),
        );
        f.set_terminator(entry, Terminator::invoke(span, call, normal, error));
        terminate_return(&mut f, normal, span);
        terminate_return(&mut f, error, span);
        verify(f);
    }

    #[test]
    #[should_panic(expected = "source fallibility and Invoke form disagree")]
    fn rejects_infallible_invoke() {
        let span = Location::new_synthesized();
        let mut f = FunctionBuilder::new("bad_invoke".into(), Default::default());
        let entry = f.add_block();
        let normal = f.add_block();
        let error = f.add_block();
        let result = append_result(&mut f, entry, Operation::alloca(span, int_type()));
        let call = Operation::call(
            span,
            Value::Function(FunctionId::new(
                ModuleId::default(),
                LocalFunctionId::default(),
            )),
            [result],
            CallImplType::value(FnType::new_by_val([], int_type(), no_effects())),
        );
        f.set_terminator(entry, Terminator::invoke(span, call, normal, error));
        terminate_return(&mut f, normal, span);
        f.set_terminator(error, Terminator::propagate_error(span));
        verify(f);
    }

    #[test]
    #[should_panic(expected = "failure_during_cleanup requires two source failures")]
    fn rejects_failure_during_cleanup_without_two_source_failures() {
        let span = Location::new_synthesized();
        let mut f = FunctionBuilder::new("bad_cleanup_failure".into(), Default::default());
        let block = f.add_block();
        f.set_terminator(block, Terminator::failure_during_cleanup(span));
        verify(f);
    }

    #[test]
    #[should_panic(expected = "must have exactly one consuming use")]
    fn rejects_unconsumed_owned_register() {
        let span = Location::new_synthesized();
        let mut f = FunctionBuilder::new("bad_register_lifetime".into(), Default::default());
        let block = f.add_block();
        append(
            &mut f,
            block,
            Operation::variant(span, ustr::ustr("A"), managed_variant_ty()),
        );
        terminate_return(&mut f, block, span);
        verify(f);
    }

    #[test]
    #[should_panic(
        expected = "stack_restore reclaims storage with a live semantic drop obligation"
    )]
    fn rejects_stack_restore_across_live_owned_storage() {
        let span = Location::new_synthesized();
        let mut f = FunctionBuilder::new("bad_stack_restore".into(), Default::default());
        let variant_ty = managed_variant_ty();
        let block = f.add_block();
        let marker = append_result(&mut f, block, Operation::stack_save(span));
        let local = append_result(&mut f, block, Operation::alloca(span, variant_ty));
        let value = append_result(
            &mut f,
            block,
            Operation::variant(span, ustr::ustr("A"), variant_ty),
        );
        append(&mut f, block, Operation::store(span, value, local));
        append(&mut f, block, Operation::stack_restore(span, marker));
        terminate_return(&mut f, block, span);
        verify(f);
    }

    #[test]
    fn permits_reusing_a_stack_marker() {
        let span = Location::new_synthesized();
        let mut f = FunctionBuilder::new("reused_stack_marker".into(), Default::default());
        let block = f.add_block();
        let marker = append_result(&mut f, block, Operation::stack_save(span));

        append(&mut f, block, Operation::alloca(span, int_type()));
        append(
            &mut f,
            block,
            Operation::stack_restore(span, marker.clone()),
        );

        append(&mut f, block, Operation::alloca(span, int_type()));
        append(&mut f, block, Operation::stack_restore(span, marker));
        terminate_return(&mut f, block, span);
        verify(f);
    }

    #[test]
    fn permits_stack_save_after_conditional_allocation() {
        let span = Location::new_synthesized();
        let session = CompilerSession::new();
        let env = session.module_env();
        let mut f = FunctionBuilder::new("conditional_stack_allocation".into(), Default::default());
        let condition = f.add_constant(
            crate::std::logic::bool_type(),
            LiteralValue::new_native(true),
            &env,
        );
        let entry = f.add_block();
        let allocated = f.add_block();
        let skipped = f.add_block();
        let join = f.add_block();

        f.set_terminator(
            entry,
            Terminator::cond_br(
                span,
                crate::mir::Value::Constant(condition),
                allocated,
                skipped,
            ),
        );
        append(&mut f, allocated, Operation::alloca(span, int_type()));
        f.set_terminator(allocated, Terminator::goto(span, join));
        f.set_terminator(skipped, Terminator::goto(span, join));
        append(&mut f, join, Operation::stack_save(span));
        terminate_return(&mut f, join, span);
        verify(f);
    }

    #[test]
    #[should_panic(expected = "clear discards a live semantic drop obligation")]
    fn rejects_clearing_owned_storage_without_drop() {
        let span = Location::new_synthesized();
        let mut f = FunctionBuilder::new("bad_clear".into(), Default::default());
        let variant_ty = managed_variant_ty();
        let block = f.add_block();
        let local = append_result(&mut f, block, Operation::alloca(span, variant_ty));
        let value = append_result(
            &mut f,
            block,
            Operation::variant(span, ustr::ustr("A"), variant_ty),
        );
        append(&mut f, block, Operation::store(span, value, local.clone()));
        append(&mut f, block, Operation::clear(span, local));
        terminate_return(&mut f, block, span);
        verify(f);
    }
}
