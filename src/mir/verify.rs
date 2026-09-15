// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Derived structural and ownership verification for MIR functions.
//!
//! The verifier deliberately keeps initialization/drop state out of [`Function`]. MIR operations
//! (`store`, `move`, `drop`, `clear`, …) are the source of truth; this module derives their effects
//! per function and checks them before execution. A later backend may lower the same abstract state
//! to concrete drop flags without exposing those flags to optimization-oriented MIR.

use std::{
    collections::{VecDeque, hash_map::Entry},
    fmt,
    iter::once,
};

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    format::FormatWith,
    mir::{
        self, BlockId, Function, Instantiation, Operation, OperationKind, OperationResult,
        ParameterId, ParameterKind, ValueId,
        dominance::Dominance,
        operation::SourceFallibility,
        role::{self, MirType, ValueRole, ValueRoles},
        terminator::TerminatorKind,
    },
    module::{ModuleEnv, id::Id},
    std::array::array_type,
    types::{
        effects::{Effect, PrimitiveEffect},
        r#type::{CallImplType, CallResultConvention, Type, TypeKind},
        type_like::TypeLike,
        type_properties::concrete_type_is_trivial_copy,
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
#[cfg(any(debug_assertions, test))]
pub(crate) fn verify_function(func: &Function, env: ModuleEnv<'_>) {
    Verifier::new(func, env).verify(true, None);
}

/// Verifies semantic MIR using the roles from a pre-check of this exact, unchanged function body.
#[cfg(any(debug_assertions, test, feature = "std-snapshot"))]
pub(crate) fn verify_function_with_roles(func: &Function, env: ModuleEnv<'_>, roles: ValueRoles) {
    Verifier::new(func, env).verify(true, Some(roles));
}

/// Physical lowering preserves SSA, operand roles, source-failure flow, and register ownership.
/// Semantic field-path storage analysis no longer applies after projections become byte offsets;
/// physical storage initialization and lifetime must be checked by the executor instead.
pub(crate) fn verify_physical_function(func: &Function, env: ModuleEnv<'_>) {
    // Diagnose the offending operand slot before type/dataflow analyses see its consequences.
    let roles = role::check_function_operand_roles(func);
    Verifier::new(func, env).verify(false, Some(roles));
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

/// Representation compatibility is verification-only: it needs a [`ModuleEnv`] to walk the type
/// graph, so it stays here rather than in [`role`](crate::mir::role), which lowering also uses.
impl MirType {
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

/// Path-sensitive lifetime state of one owned SSA register.
///
/// `NOT_PRODUCED | CONSUMED` naturally occurs at a loop header: the first iteration has not run the
/// definition yet, while a backedge has already consumed the previous iteration's value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct OwnedRegisterState(u8);

impl OwnedRegisterState {
    const NOT_PRODUCED: Self = Self(1 << 0);
    const LIVE: Self = Self(1 << 1);
    const CONSUMED: Self = Self(1 << 2);

    fn join(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    fn may_be_live(self) -> bool {
        self.0 & Self::LIVE.0 != 0
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RegisterOwnershipState {
    registers: FxHashMap<ValueId, OwnedRegisterState>,
}

impl RegisterOwnershipState {
    fn join(&mut self, other: &Self) -> bool {
        debug_assert_eq!(self.registers.len(), other.registers.len());
        let mut changed = false;
        for (register, state) in &mut self.registers {
            let joined = state.join(other.registers[register]);
            changed |= joined != *state;
            *state = joined;
        }
        changed
    }
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

struct RootInfo {
    value: mir::Value,
    ty: Type,
    /// Owned parameters enter live; local allocations enter unallocated.
    initially_live: bool,
    /// Whether every ownership-relevant subplace of this root is represented precisely by
    /// `StorageState`. Opaque native/custom/variant interiors are still checked at individual
    /// operations, but cannot prove whole-frame absence at exit.
    exact: bool,
}

type NodeId = usize;

/// Renders a node index the way verification diagnostics name it.
struct NodeAt(NodeId);

impl fmt::Display for NodeAt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "node {}", self.0)
    }
}

#[derive(Clone, Copy)]
enum NodeLocation {
    Operation { block: BlockId, index: usize },
    Terminator { block: BlockId },
}

struct Verifier<'a> {
    func: &'a Function,
    env: ModuleEnv<'a>,
    nodes: Vec<NodeLocation>,
    node_order: Vec<NodeId>,
    node_index: FxHashMap<NodeId, usize>,
    node_block: FxHashMap<NodeId, BlockId>,
    block_first: FxHashMap<BlockId, NodeId>,
    value_definition: FxHashMap<ValueId, NodeId>,
    roles: ValueRoles,
    roots: Vec<RootInfo>,
    root_index: FxHashMap<mir::Value, usize>,
    trivial_copy: FxHashMap<Type, bool>,
}

impl<'a> Verifier<'a> {
    fn new(func: &'a Function, env: ModuleEnv<'a>) -> Self {
        Self {
            func,
            env,
            nodes: vec![],
            node_order: vec![],
            node_index: FxHashMap::default(),
            node_block: FxHashMap::default(),
            block_first: FxHashMap::default(),
            value_definition: FxHashMap::default(),
            roles: ValueRoles::default(),
            roots: vec![],
            root_index: FxHashMap::default(),
            trivial_copy: FxHashMap::default(),
        }
    }

    fn verify(mut self, semantic_storage: bool, roles: Option<ValueRoles>) {
        self.verify_shared_contracts(roles);
        if semantic_storage {
            self.collect_storage_roots();
            self.verify_storage_ownership();
        }
    }

    fn verify_shared_contracts(&mut self, roles: Option<ValueRoles>) {
        self.verify_structure();
        self.collect_value_information(roles);
        self.verify_operand_roles_and_dominance();
        self.verify_source_failure_flow();
        self.verify_register_ownership();
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
                TerminatorKind::SwitchVariant { cases, default, .. } => cases
                    .iter()
                    .map(|(_, target)| (*target, state))
                    .chain(once((*default, state)))
                    .collect(),
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
                TerminatorKind::InvariantFailure { .. } => vec![],
            };

            for (successor, successor_state) in successors {
                match inputs.entry(successor) {
                    Entry::Vacant(entry) => {
                        entry.insert(successor_state);
                        worklist.push_back(successor);
                    }
                    Entry::Occupied(entry) => assert_eq!(
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
                TerminatorKind::SwitchVariant { cases, default, .. } => {
                    assert!(
                        cases.iter().all(|(_, target)| target_ok(*target)) && target_ok(*default),
                        "MIR function `{}` block {}: switch_variant targets a missing block",
                        self.func.name,
                        block.as_u32()
                    );
                    let mut tags = FxHashSet::default();
                    assert!(
                        cases.iter().all(|(tag, _)| tags.insert(*tag)),
                        "MIR function `{}` block {}: switch_variant has a duplicate case",
                        self.func.name,
                        block.as_u32()
                    );
                }
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

    fn collect_value_information(&mut self, roles: Option<ValueRoles>) {
        // Without a role pre-check, malformed structure must be diagnosed before role resolution.
        self.roles = roles.unwrap_or_else(|| ValueRoles::derive(self.func));
        for index in 0..self.node_order.len() {
            let node = self.node_order[index];
            let Some(mir::Value::Register(value_id)) = self.definition(node) else {
                continue;
            };
            assert!(
                self.value_definition.insert(value_id, node).is_none(),
                "MIR function `{}`: value {value_id} has more than one definition",
                self.func.name
            );
        }
    }

    /// Storage paths and their type properties are only needed by semantic storage analysis.
    /// Physical verification does not need them, since its storage is byte-offset-based.
    fn collect_storage_roots(&mut self) {
        for index in 0..self.func.parameters().len() {
            let parameter = &self.func.parameters()[index];
            if !matches!(parameter.kind, ParameterKind::Owned) {
                continue;
            }
            let ty = parameter.ty;
            let value = mir::Value::Parameter(ParameterId::from_index(index));
            let root = self.roots.len();
            let exact = self.storage_paths_are_exact(ty, &mut Vec::new());
            self.roots.push(RootInfo {
                value: value.clone(),
                ty,
                initially_live: true,
                exact,
            });
            self.root_index.insert(value, root);
        }

        for index in 0..self.node_order.len() {
            let node = self.node_order[index];
            let Some(value) = self.definition(node) else {
                continue;
            };
            if let OperationKind::Alloca { ty } = self.operation(node).unwrap().kind {
                let root = self.roots.len();
                let exact = self.storage_paths_are_exact(ty, &mut Vec::new());
                self.roots.push(RootInfo {
                    value: value.clone(),
                    ty,
                    initially_live: false,
                    exact,
                });
                self.root_index.insert(value, root);
            }
        }
    }

    fn role(&self, value: &mir::Value) -> ValueRole {
        self.roles
            .expect(self.func.name, value, self.func.constants())
            .into_owned()
    }

    fn materialized_type(&self, value: &mir::Value) -> Option<MirType> {
        self.role(value).materialized_type().cloned()
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

    /// Verifies the parts of an operation's operand contract that need a [`ModuleEnv`].
    ///
    /// The role half — which slot must hold a place, a value, or evidence — lives in
    /// [`role::check_operand_roles`], which lowering also runs at insertion in debug and test
    /// builds. What remains here is representation compatibility and the metadata cross-checks,
    /// which need the type graph.
    fn verify_node_roles(&self, node: NodeId) {
        let constants = self.func.constants();
        let at = NodeAt(node);
        let Some(whole) = self.operation(node) else {
            role::check_terminator_operand_roles(
                &self.roles,
                self.func.name,
                &at,
                self.terminator(node).unwrap(),
                constants,
            );
            return;
        };
        role::check_operand_roles(&self.roles, self.func.name, &at, whole, constants);

        let invoked = matches!(self.terminator(node), Some(TerminatorKind::Invoke { .. }));
        assert_eq!(
            invoked,
            self.operation_is_source_fallible(whole),
            "MIR function `{}` node {}: source fallibility and Invoke form disagree",
            self.func.name,
            node
        );

        let operands = self.operands(node);
        match &whole.kind {
            OperationKind::BuildArray { element_ty } => {
                assert!(
                    concrete_type_is_trivial_copy(*element_ty, &self.env),
                    "MIR function `{}` node {}: build_array element type must be statically TrivialCopy",
                    self.func.name,
                    node
                );
                let (destination, elements) = operands
                    .split_last()
                    .expect("build_array has a trailing destination");
                let expected = MirType::Lowered(*element_ty);
                for (index, element) in elements.iter().enumerate() {
                    let role = self.role(element);
                    let actual = role
                        .inner_type()
                        .expect("build_array element roles were checked above");
                    assert!(
                        actual.representation_compatible(&expected, &self.env),
                        "MIR function `{}` node {}: build_array element operand {} has representation {}, expected {}",
                        self.func.name,
                        node,
                        index,
                        actual.format(&self.env),
                        expected.format(&self.env)
                    );
                }
                self.verify_place_representation(
                    node,
                    operands.len() - 1,
                    destination,
                    MirType::Lowered(array_type(*element_ty)),
                );
            }
            OperationKind::Call { ty, metadata } => {
                self.verify_instantiation(
                    node,
                    &operands[0],
                    ty,
                    metadata
                        .as_deref()
                        .and_then(|metadata| metadata.instantiation.as_ref()),
                );
                let visible_start = operands.len() - ty.fn_ty.args.len() - 1;
                for (offset, argument) in ty.fn_ty.args.iter().enumerate() {
                    let index = visible_start + offset;
                    self.verify_place_representation(
                        node,
                        index,
                        &operands[index],
                        MirType::Lowered(argument.ty),
                    );
                }
                if let Some(metadata) = metadata {
                    for argument in metadata.owned_arguments.iter_ones() {
                        assert!(
                            argument < ty.fn_ty.args.len(),
                            "MIR function `{}` node {}: owned call argument {} is out of range",
                            self.func.name,
                            node,
                            argument
                        );
                        assert!(
                            !ty.fn_ty.args[argument]
                                .mut_ty
                                .as_resolved()
                                .is_some_and(|mutability| mutability.is_mutable()),
                            "MIR function `{}` node {}: a mutable-reference argument cannot transfer ownership",
                            self.func.name,
                            node
                        );
                    }
                }
                if ty.fn_ty.ret != Type::never() {
                    let expected = if ty.result_convention.returns_place() {
                        MirType::pointer_to(MirType::Lowered(ty.fn_ty.ret))
                    } else {
                        MirType::Lowered(ty.fn_ty.ret)
                    };
                    self.verify_place_representation(
                        node,
                        operands.len() - 1,
                        operands.last().unwrap(),
                        expected,
                    );
                }
            }
            OperationKind::Project { yielded, ty } => {
                assert_eq!(
                    ty.result_convention,
                    CallResultConvention::YIELDED_ONCE,
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
                let visible_start = operands.len() - ty.fn_ty.args.len();
                for (offset, argument) in ty.fn_ty.args.iter().enumerate() {
                    let index = visible_start + offset;
                    self.verify_place_representation(
                        node,
                        index,
                        &operands[index],
                        MirType::Lowered(argument.ty),
                    );
                }
            }
            OperationKind::Store => {
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
            OperationKind::Memcpy | OperationKind::Move | OperationKind::Replace => {
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
            }
            OperationKind::MoveBytes { ty } => {
                self.verify_place_representation(node, 0, &operands[0], MirType::Lowered(*ty));
                self.verify_place_representation(node, 1, &operands[1], MirType::Lowered(*ty));
            }
            _ => {}
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

    /// Dominance over *instructions*, not blocks: an invoked operation's result is anchored at
    /// its normal successor and must not reach the error one, which a block-level tree cannot say.
    fn compute_instruction_dominance(&self) -> Dominance {
        let node_count = self.node_order.len();
        let entry = self.node_index[&self.block_first[&self.func.entry()]];
        let mut successors = vec![Vec::new(); node_count];
        for (node_index, &node) in self.node_order.iter().enumerate() {
            for (successor, _) in self.successors(node) {
                let successor = self.node_index[&successor];
                if !successors[node_index].contains(&successor) {
                    successors[node_index].push(successor);
                }
            }
        }
        Dominance::of(&successors, entry)
    }

    /// Whether a place holds a *bare* function value — a code identity with no owned environment.
    ///
    /// A function type is never `TrivialCopy`, because nothing in `(A) -> int` says whether the
    /// value carries a captured environment, and copying one by representation would duplicate an
    /// environment its storage owns. A dictionary method slot is where the type is silent but the
    /// contract is not: a dictionary holds trait method function values, which are code identities
    /// and never closures — the same contract [`Operation::call`] states when it admits "a method
    /// slot `project`ed out of a dictionary" as a callee. Reading one as a first-class value is
    /// therefore a representation copy, and the drop its consumer emits finds no environment to
    /// release.
    ///
    /// A closure is unaffected: it lives in ordinary storage, is reached through its own place, and
    /// is copied through `Value::clone` like any other owned value.
    fn is_bare_function_slot(&self, value: &mir::Value) -> bool {
        let mir::Value::Register(id) = value else {
            return false;
        };
        let Some(node) = self.value_definition.get(id) else {
            return false;
        };
        matches!(
            self.operation(*node).map(|op| &op.kind),
            Some(OperationKind::DictEntry { .. })
        )
    }

    fn place_pointee_type(&self, value: &mir::Value) -> Option<MirType> {
        self.role(value).place_pointee_type()
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
        instantiation: Option<&Instantiation>,
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

    /// Verifies that every executed owned-register definition is consumed exactly once on each
    /// returning path. A definition may have several syntactic consumers in mutually exclusive
    /// blocks; joins retain whether any incoming path is still live.
    fn verify_register_ownership(&self) {
        let initial = RegisterOwnershipState {
            registers: self
                .node_order
                .iter()
                .copied()
                .filter(|node| self.register_needs_consuming_use(*node))
                .map(|node| {
                    let mir::Value::Register(register) = self.definition(node).unwrap() else {
                        unreachable!("operation results are registers")
                    };
                    (register, OwnedRegisterState::NOT_PRODUCED)
                })
                .collect(),
        };
        if initial.registers.is_empty() {
            return;
        }

        let mut inputs: Vec<Option<RegisterOwnershipState>> = vec![None; self.node_order.len()];
        let entry = self.block_first[&self.func.entry()];
        inputs[self.node_index[&entry]] = Some(initial);
        let mut worklist = VecDeque::from([entry]);

        while let Some(node) = worklist.pop_front() {
            let index = self.node_index[&node];
            let mut state = inputs[index]
                .clone()
                .expect("ownership worklist nodes have an input state");

            for (operand_index, operand) in self.operands(node).iter().enumerate() {
                let mir::Value::Register(register) = operand else {
                    continue;
                };
                let Some(register_state) = state.registers.get_mut(register) else {
                    continue;
                };
                assert_eq!(
                    *register_state,
                    OwnedRegisterState::LIVE,
                    "MIR function `{}` node {}: use of owned register {} while its state is {:?}",
                    self.func.name,
                    node,
                    operand,
                    register_state
                );
                if self
                    .operation(node)
                    .is_some_and(|operation| self.operand_consumes_value(operation, operand_index))
                {
                    *register_state = OwnedRegisterState::CONSUMED;
                }
            }

            if self.register_needs_consuming_use(node) {
                let mir::Value::Register(register) = self.definition(node).unwrap() else {
                    unreachable!("operation results are registers")
                };
                let previous = state.registers[&register];
                assert!(
                    !previous.may_be_live(),
                    "MIR function `{}` node {}: owned register {} is redefined while its previous loop iteration may still be live",
                    self.func.name,
                    node,
                    register
                );
                state.registers.insert(register, OwnedRegisterState::LIVE);
            }

            if matches!(
                self.terminator(node),
                Some(TerminatorKind::Return | TerminatorKind::PropagateError)
            ) {
                let live = state
                    .registers
                    .iter()
                    .find(|(_, state)| state.may_be_live());
                assert!(
                    live.is_none(),
                    "MIR function `{}` node {}: frame exits with live owned register {}",
                    self.func.name,
                    node,
                    live.unwrap().0
                );
            }

            for (target, _) in self.successors(node) {
                let target_index = self.node_index[&target];
                let changed = match &mut inputs[target_index] {
                    Some(input) => input.join(&state),
                    slot @ None => {
                        *slot = Some(state.clone());
                        true
                    }
                };
                if changed {
                    worklist.push_back(target);
                }
            }
        }
    }

    /// Computes which saved stack-frontier registers may be read at each instruction before that
    /// static register is defined again.
    ///
    /// A `stack_save` inside a loop defines a fresh dynamic marker on every iteration. Once all
    /// uses of the current value are past, retaining its snapshot in [`AnalysisState`] only keeps
    /// dead history distinct at later joins. In particular, a marker whose snapshot depends on
    /// several earlier branches can otherwise multiply ownership alternatives on every trip
    /// around the loop. Ordinary backwards liveness proves exactly when that history is dead while
    /// preserving markers which are restored more than once.
    fn stack_marker_live_in(&self) -> Option<Vec<FxHashSet<ValueId>>> {
        let node_count = self.node_order.len();
        if !self.node_order.iter().any(|&node| {
            self.operation(node)
                .is_some_and(|operation| matches!(operation.kind, OperationKind::StackSave))
        }) {
            return None;
        }
        let mut predecessors = vec![Vec::new(); node_count];
        for &node in &self.node_order {
            let index = self.node_index[&node];
            for (successor, _) in self.successors(node) {
                predecessors[self.node_index[&successor]].push(index);
            }
        }

        let mut live_in = vec![FxHashSet::default(); node_count];
        let mut pending = VecDeque::from_iter((0..node_count).rev());
        let mut queued = vec![true; node_count];
        while let Some(index) = pending.pop_front() {
            queued[index] = false;
            let node = self.node_order[index];
            let mut live = FxHashSet::default();
            for (successor, _) in self.successors(node) {
                live.extend(live_in[self.node_index[&successor]].iter().copied());
            }
            if let Some(operation) = self.operation(node) {
                if matches!(operation.kind, OperationKind::StackSave)
                    && let Some(mir::Value::Register(marker)) = self.definition(node)
                {
                    live.remove(&marker);
                }
                if matches!(operation.kind, OperationKind::StackRestore)
                    && let Some(mir::Value::Register(marker)) = operation.operands.first()
                {
                    live.insert(*marker);
                }
            }
            if live == live_in[index] {
                continue;
            }
            live_in[index] = live;
            for &predecessor in &predecessors[index] {
                if !queued[predecessor] {
                    queued[predecessor] = true;
                    pending.push_back(predecessor);
                }
            }
        }
        Some(live_in)
    }

    fn operand_consumes_value(&self, node: &Operation, index: usize) -> bool {
        matches!(
            node.kind,
            OperationKind::Store | OperationKind::RuntimeDealloc
        ) && index == 0
    }

    fn register_needs_consuming_use(&self, node: NodeId) -> bool {
        self.operation(node)
            .is_some_and(Operation::result_requires_consuming_use)
    }

    fn verify_storage_ownership(&mut self) {
        self.verify_storage_ownership_max_alternatives();
    }

    /// Runs ownership verification and returns the largest number of relational states retained
    /// at one instruction. The count lets structural tests guard against accidentally bypassing
    /// state pruning without relying on wall-clock timing.
    fn verify_storage_ownership_max_alternatives(&mut self) -> usize {
        let roots = self
            .roots
            .iter()
            .map(|root| (root.ty, root.initially_live))
            .collect::<Vec<_>>();
        let mut initial_roots = Vec::with_capacity(roots.len());
        for (ty, initially_live) in roots {
            initial_roots.push(if initially_live {
                self.live_state_for_type(ty)
            } else {
                StorageState::shaped(ty, LeafState::UNALLOCATED, &self.env, &mut Vec::new())
            });
        }
        let initial = AnalysisState {
            roots: initial_roots,
            markers: FxHashMap::default(),
            open_projections: FxHashSet::default(),
        };
        // Keep different allocation frontiers and stack-marker snapshots as separate alternatives.
        // Merging either correlation would make it impossible to verify what a later
        // `stack_restore` reclaims. Within one alternative, ordinary ownership states still join to
        // a fixed point. Liveness prevents dead marker history from multiplying around loops, but
        // the number of states remains worst-case exponential in simultaneously live, correlated
        // frontiers.
        let mut inputs: Vec<Vec<AnalysisState>> = vec![vec![]; self.node_order.len()];
        let marker_live_in = self.stack_marker_live_in();
        let entry = self.block_first[&self.func.entry()];
        inputs[self.node_index[&entry]].push(initial);
        let mut worklist = VecDeque::from([(entry, 0)]);

        while let Some((node, alternative)) = worklist.pop_front() {
            let index = self.node_index[&node];
            let input = inputs[index][alternative].clone();
            let edges = self.transfer(node, &input);
            for (target, mut state) in edges {
                let target_index = self.node_index[&target];
                if let Some(marker_live_in) = &marker_live_in {
                    state.markers.retain(|marker, _| {
                        let mir::Value::Register(marker) = marker else {
                            // Stack saves currently define registers exclusively. Preserve any
                            // future marker form conservatively instead of silently pruning it.
                            return true;
                        };
                        marker_live_in[target_index].contains(marker)
                    });
                }
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

        inputs.iter().map(Vec::len).max().unwrap_or(0)
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
                OperationKind::RuntimeAlloc { .. } | OperationKind::RuntimeDealloc => {}
                OperationKind::Store => {
                    self.transfer_store(&operands[0], &operands[1], &mut normal);
                }
                OperationKind::Memcpy => {
                    if let Some(MirType::Lowered(ty)) = self.place_pointee_type(&operands[0]) {
                        assert!(
                            self.is_trivial_copy(ty) || self.is_bare_function_slot(&operands[0]),
                            "MIR function `{}`: memcpy source type is not TrivialCopy",
                            self.func.name
                        );
                    }
                    self.transfer_copy_or_move(&operands[0], &operands[1], false, &mut normal);
                }
                OperationKind::Move => {
                    self.transfer_copy_or_move(&operands[0], &operands[1], true, &mut normal);
                }
                OperationKind::Replace => {
                    self.transfer_replace(&operands[0], &operands[1], &mut normal);
                }
                OperationKind::MoveBytes { .. } => {
                    self.transfer_copy_or_move(&operands[0], &operands[1], true, &mut normal);
                }
                OperationKind::Clear => {
                    self.transfer_clear(&operands[0], &mut normal);
                }
                OperationKind::Drop { .. } => {
                    self.transfer_drop(&operands[0], &mut normal);
                    self.transfer_drop(&operands[0], &mut unwind);
                }
                OperationKind::DropSubscriptEnv => {
                    self.transfer_drop(&operands[0], &mut normal);
                    self.transfer_drop(&operands[0], &mut unwind);
                }
                // Dropping a closure environment leaves a valid environment-less function value
                // in the target place, so it does not end that place's initialized lifetime.
                OperationKind::DropClosureEnv => {}
                // The destination takes on the obligation the copy creates, exactly as a call's
                // result place does — a clone *is* a call to `Value::clone`, spelled as an
                // operation so its subject is legible.
                OperationKind::Clone { .. } => {
                    self.initialize_call_result(node, &operands[1], &mut normal);
                }
                OperationKind::BuildArray { .. } => {
                    let destination = operands
                        .last()
                        .expect("build_array has a trailing destination");
                    self.initialize_call_result(node, destination, &mut normal);
                }
                OperationKind::Call { ty, metadata } => {
                    if let Some(metadata) = metadata {
                        let visible_start = operands.len() - (ty.fn_ty.args.len() + 1);
                        for argument in metadata.owned_arguments.iter_ones() {
                            let source = &operands[visible_start + argument];
                            self.consume_place(source, &mut normal);
                            self.consume_place(source, &mut unwind);
                        }
                    }
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
            Some(TerminatorKind::InvariantFailure { .. }) => {
                // Fatal termination has no observable frame/result or ownership obligations.
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

        // A self-move reads initialized storage but leaves it unchanged, matching the boxed
        // executor's take-then-store semantics. Resolve aliases when their paths are known.
        if is_move
            && (source == destination
                || matches!(
                    (&source_place, &destination_place),
                    (LocalPlace::Root { root: left, path: Some(left_path) },
                     LocalPlace::Root { root: right, path: Some(right_path) })
                        if left == right && left_path == right_path
                ))
        {
            return;
        }

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

    fn transfer_replace(
        &mut self,
        replacement: &mir::Value,
        destination: &mir::Value,
        state: &mut AnalysisState,
    ) {
        let LocalPlace::Root {
            root,
            path: Some(path),
        } = self.local_place(replacement)
        else {
            panic!(
                "MIR function `{}`: replace requires an owned replacement",
                self.func.name
            );
        };
        assert!(
            path.is_empty(),
            "replace replacement must be a whole owned value"
        );
        let new_value = state.roots[root].clone();
        assert!(
            new_value.state.is_definitely_live(),
            "MIR function `{}`: replace replacement is not initialized",
            self.func.name
        );
        let old_value = match self.local_place(destination) {
            LocalPlace::Root {
                root: target,
                path: Some(target_path),
            } => {
                assert_ne!(root, target, "replace replacement aliases its destination");
                if let Some(old_value) = state.roots[target].at_path(&target_path).cloned() {
                    // Only the replacement must be fully live. The displaced value retains any
                    // absent fields, so subsequent cleanup observes the old initialization state.
                    assert!(
                        !old_value.state.may_be_unallocated(),
                        "replace destination is unallocated"
                    );
                    state.roots[target].replace_path(&target_path, &new_value);
                    old_value
                } else {
                    self.mark_opaque_projection_live(target, &target_path, state);
                    self.live_state_for_type(new_value.ty)
                }
            }
            _ => self.live_state_for_type(new_value.ty),
        };
        state.roots[root].replace_path(&[], &old_value);
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
            "MIR function `{}`: ownership transfer consumes storage that is not definitely initialized",
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
            if self.roots[index].initially_live {
                assert_eq!(
                    root.state,
                    LeafState::ABSENT,
                    "MIR function `{}` node {}: frame exits without consuming owned parameter {}",
                    self.func.name,
                    node,
                    self.roots[index].value
                );
                continue;
            }
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
            | mir::Value::Evidence(_)
            | mir::Value::Pattern(_) => false,
            mir::Value::Parameter(_) => false,
            mir::Value::Register(value_id) => {
                let node = self.value_definition[value_id];
                let operation = self.operation(node).unwrap();
                match &operation.kind {
                    OperationKind::Variant { metadata, .. } => !self.is_trivial_copy(metadata.ty),
                    OperationKind::CloneClosureEnv { .. } => true,
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
                    | OperationKind::BuildSubscriptEvidence { .. } => false,
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
        let result = concrete_type_is_trivial_copy(ty, &self.env);
        self.trivial_copy.insert(ty, result);
        result
    }

    fn local_place(&self, value: &mir::Value) -> LocalPlace {
        if let mir::Value::Parameter(id) = value {
            return if matches!(
                self.func.parameters()[id.as_index()].kind,
                ParameterKind::Owned
            ) {
                LocalPlace::Root {
                    root: self.root_index[value],
                    path: Some(vec![]),
                }
            } else {
                LocalPlace::External
            };
        }
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
            Some(TerminatorKind::SwitchVariant { cases, default, .. }) => {
                result.extend(
                    cases
                        .iter()
                        .map(|(_, target)| (first(target), EdgeKind::Normal)),
                );
                result.push((first(default), EdgeKind::Normal));
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
                | TerminatorKind::FailureDuringCleanup
                | TerminatorKind::InvariantFailure { .. },
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
    use ustr::ustr;

    use super::{Verifier, verify_function};
    use crate::{
        CompilerSession, Location,
        hir::{
            function::ArgConvention,
            value::{LiteralValue, VariantPayloadStorage},
        },
        mir::{
            BlockId, Operation, ParameterKind, Value, builder::FunctionBuilder, edit::FunctionEdit,
            terminator::Terminator,
        },
        module::{FunctionId, LocalFunctionId, ModuleId},
        std::{logic::bool_type, math::int_type, string::string_type},
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

    #[test]
    fn self_move_preserves_initialized_storage() {
        let span = Location::new_synthesized();
        let mut f = FunctionBuilder::new("self_move".into(), Default::default());
        let source = Value::Parameter(f.add_parameter(int_type(), ParameterKind::Owned));
        let result = Value::Parameter(f.add_parameter(int_type(), ParameterKind::Return));
        let block = f.add_block();
        append(
            &mut f,
            block,
            Operation::move_value(span, source.clone(), source.clone()),
        );
        // Reading the source afterwards must remain valid; moving it to the result also discharges
        // the owned parameter's obligation instead of allowing a self-move to consume it.
        append(&mut f, block, Operation::move_value(span, source, result));
        terminate_return(&mut f, block, span);
        verify(f);
    }

    /// A variant that owns something, so these tests have a drop obligation to violate. The payload
    /// is load-bearing: a sum type with only trivial inline payloads has no drop obligation.
    fn managed_variant_ty() -> Type {
        Type::variant([(ustr("A"), string_type())])
    }

    fn replace_body(initialized: bool, aliases: bool) -> FunctionBuilder {
        let session = CompilerSession::new();
        let span = Location::new_synthesized();
        let mut f = FunctionBuilder::new("replace_test".into(), Default::default());
        let destination = Value::Parameter(f.add_parameter(
            int_type(),
            ParameterKind::Parameter(ArgConvention::MutableRef),
        ));
        let block = f.add_block();
        let replacement = append_result(&mut f, block, Operation::alloca(span, int_type()));
        if initialized {
            let value = f.add_constant(
                int_type(),
                LiteralValue::new_native(7isize),
                &session.module_env(),
            );
            append(
                &mut f,
                block,
                Operation::store(span, Value::Constant(value), replacement.clone()),
            );
        }
        let destination = if aliases {
            replacement.clone()
        } else {
            destination
        };
        append(
            &mut f,
            block,
            Operation::replace(span, replacement, destination, None),
        );
        terminate_return(&mut f, block, span);
        f
    }

    #[test]
    fn replace_accepts_a_prepared_owned_replacement() {
        verify(replace_body(true, false));
    }

    #[test]
    fn replace_accepts_absent_and_partially_initialized_destinations() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        let ty = Type::tuple([int_type(), int_type()]);
        for initialized_fields in 0..=1 {
            let mut f = FunctionBuilder::new("partial_replace".into(), Default::default());
            let replacement = Value::Parameter(f.add_parameter(ty, ParameterKind::Owned));
            let result = Value::Parameter(f.add_parameter(ty, ParameterKind::Return));
            let block = f.add_block();
            let destination = append_result(&mut f, block, Operation::alloca(span, ty));
            let zero =
                Value::Constant(f.add_constant(int_type(), LiteralValue::new_native(0isize), &env));
            for _ in 0..initialized_fields {
                let field = append_result(
                    &mut f,
                    block,
                    Operation::product_subfield(
                        span,
                        destination.clone(),
                        zero.clone(),
                        int_type(),
                        ty,
                        [],
                    ),
                );
                append(&mut f, block, Operation::store(span, zero.clone(), field));
            }
            append(
                &mut f,
                block,
                Operation::replace(span, replacement.clone(), destination.clone(), None),
            );
            // The destination is now fully live, even though its previous state was not.
            append(
                &mut f,
                block,
                Operation::move_value(span, destination, result),
            );
            if initialized_fields == 1 {
                let old_field = append_result(
                    &mut f,
                    block,
                    Operation::product_subfield(
                        span,
                        replacement.clone(),
                        zero,
                        int_type(),
                        ty,
                        [],
                    ),
                );
                let scratch = append_result(&mut f, block, Operation::alloca(span, int_type()));
                append(
                    &mut f,
                    block,
                    Operation::move_value(span, old_field, scratch),
                );
            }
            append(&mut f, block, Operation::clear(span, replacement));
            terminate_return(&mut f, block, span);
            f.finish(env);
        }
    }

    #[test]
    #[should_panic(expected = "move reads storage that is not definitely initialized")]
    fn replace_preserves_the_displaced_values_absence() {
        let span = Location::new_synthesized();
        let mut f = FunctionBuilder::new("absent_displaced_value".into(), Default::default());
        let replacement = Value::Parameter(f.add_parameter(int_type(), ParameterKind::Owned));
        let block = f.add_block();
        let destination = append_result(&mut f, block, Operation::alloca(span, int_type()));
        append(
            &mut f,
            block,
            Operation::replace(span, replacement.clone(), destination.clone(), None),
        );
        // The new destination is live, but the displaced value is absent, not invented data.
        append(
            &mut f,
            block,
            Operation::move_value(span, replacement, destination),
        );
        terminate_return(&mut f, block, span);
        verify(f);
    }

    #[test]
    #[should_panic(expected = "replace replacement is not initialized")]
    fn replace_rejects_an_uninitialized_replacement() {
        verify(replace_body(false, false));
    }

    #[test]
    #[should_panic(expected = "replace replacement aliases its destination")]
    fn replace_rejects_aliasing_storage() {
        verify(replace_body(true, true));
    }

    #[test]
    #[should_panic(expected = "replace requires an owned replacement")]
    fn replace_rejects_a_borrowed_replacement() {
        let span = Location::new_synthesized();
        let mut f = FunctionBuilder::new("borrowed_replace".into(), Default::default());
        let kind = ParameterKind::Parameter(ArgConvention::MutableRef);
        let first = Value::Parameter(f.add_parameter(int_type(), kind));
        let second = Value::Parameter(f.add_parameter(int_type(), kind));
        let block = f.add_block();
        append(&mut f, block, Operation::replace(span, first, second, None));
        terminate_return(&mut f, block, span);
        verify(f);
    }

    #[test]
    #[should_panic(expected = "without consuming owned parameter")]
    fn replace_retains_the_old_values_drop_obligation() {
        let span = Location::new_synthesized();
        let mut f = FunctionBuilder::new("leaked_replace".into(), Default::default());
        let first = Value::Parameter(f.add_parameter(string_type(), ParameterKind::Owned));
        let second = Value::Parameter(f.add_parameter(
            string_type(),
            ParameterKind::Parameter(ArgConvention::MutableRef),
        ));
        let block = f.add_block();
        append(&mut f, block, Operation::replace(span, first, second, None));
        terminate_return(&mut f, block, span);
        verify(f);
    }

    #[test]
    fn invariant_failure_allows_live_storage_and_an_uninitialized_result() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        let mut f = FunctionBuilder::new(ustr("fatal"), CallResultConvention::Value);
        f.add_parameter(string_type(), ParameterKind::Return);
        let block = f.add_block();
        let variant_ty = managed_variant_ty();
        let place = append_result(&mut f, block, Operation::alloca(span, variant_ty));
        let value = append_result(
            &mut f,
            block,
            Operation::variant(
                span,
                ustr("A"),
                variant_ty,
                string_type(),
                Some(VariantPayloadStorage::Inline),
                None,
                None,
            ),
        );
        append(&mut f, block, Operation::store(span, value, place));
        f.set_terminator(
            block,
            Terminator::invariant_failure(span, ustr("broken invariant")),
        );
        f.finish(env);
    }

    #[test]
    #[should_panic(expected = "operand 0 must be evidence")]
    fn rejects_materialized_variant_storage_operand() {
        let span = Location::new_synthesized();
        let session = CompilerSession::new();
        let env = session.module_env();
        let mut f = FunctionBuilder::new("bad_variant_evidence".into(), Default::default());
        let storage = f.add_constant(bool_type(), LiteralValue::new_native(false), &env);
        let variant_ty = Type::variant([(ustr("A"), Type::unit())]);
        let block = f.add_block();
        append(
            &mut f,
            block,
            Operation::variant(
                span,
                ustr("A"),
                variant_ty,
                Type::unit(),
                None,
                Some(Value::Constant(storage)),
                None,
            ),
        );
        terminate_return(&mut f, block, span);
        f.finish(env);
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
            Operation::variant(
                span,
                ustr("A"),
                variant_ty,
                string_type(),
                Some(VariantPayloadStorage::Inline),
                None,
                None,
            ),
        );
        append(&mut f, block, Operation::store(span, first, local.clone()));
        let second = append_result(
            &mut f,
            block,
            Operation::variant(
                span,
                ustr("A"),
                variant_ty,
                string_type(),
                Some(VariantPayloadStorage::Inline),
                None,
                None,
            ),
        );
        append(&mut f, block, Operation::store(span, second, local));
        append(
            &mut f,
            block,
            Operation::store(span, Value::Constant(constant), Value::Parameter(ret)),
        );
        terminate_return(&mut f, block, span);
        verify(f);
    }

    #[test]
    #[should_panic(expected = "load takes exactly the source place")]
    fn semantic_verification_checks_structure_before_deriving_roles() {
        let session = CompilerSession::new();
        let span = Location::new_synthesized();
        let mut f = FunctionBuilder::new("bad_load_shape".into(), Default::default());
        let block = f.add_block();
        let marker = append_result(&mut f, block, Operation::stack_save(span));
        let slot = append_result(&mut f, block, Operation::alloca(span, int_type()));
        append_result(&mut f, block, Operation::load(span, slot));
        terminate_return(&mut f, block, span);
        let mut edit = FunctionEdit::new(f.finish_unverified());
        // Both the operand count and pointee role are invalid. The structural diagnostic must win.
        edit.block_mut(block).operations[2].operands =
            vec![marker.clone(), marker].into_boxed_slice();
        verify_function(&edit.finish_unverified(), session.module_env());
    }

    #[test]
    #[should_panic(expected = "does not dominate")]
    fn rejects_register_use_not_dominated_by_its_definition() {
        let span = Location::new_synthesized();
        let session = CompilerSession::new();
        let env = session.module_env();
        let mut f = FunctionBuilder::new("bad_dominance".into(), Default::default());
        let condition = f.add_constant(bool_type(), LiteralValue::new_native(true), &env);
        let variant_ty = managed_variant_ty();
        let entry = f.add_block();
        let defining = f.add_block();
        let using = f.add_block();
        let local = append_result(&mut f, entry, Operation::alloca(span, variant_ty));
        f.set_terminator(
            entry,
            Terminator::cond_br(span, Value::Constant(condition), defining, using),
        );
        let value = append_result(
            &mut f,
            defining,
            Operation::variant(
                span,
                ustr("A"),
                variant_ty,
                string_type(),
                Some(VariantPayloadStorage::Inline),
                None,
                None,
            ),
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
        let condition = f.add_constant(bool_type(), LiteralValue::new_native(true), &env);
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
            Operation::store(span, Value::Constant(value), local.clone()),
        );
        f.set_terminator(
            entry,
            Terminator::cond_br(span, Value::Constant(condition), left, right),
        );
        f.set_terminator(left, Terminator::goto(span, join));
        f.set_terminator(right, Terminator::goto(span, join));
        let loaded = append_result(&mut f, join, Operation::load(span, local));
        append(
            &mut f,
            join,
            Operation::store(span, loaded, Value::Parameter(ret)),
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
        let condition = f.add_constant(bool_type(), LiteralValue::new_native(true), &env);
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
            Operation::store(span, Value::Constant(value), local.clone()),
        );
        f.set_terminator(entry, Terminator::goto(span, header));
        append(&mut f, header, Operation::load(span, local.clone()));
        f.set_terminator(
            header,
            Terminator::cond_br(span, Value::Constant(condition), body, exit),
        );
        append(&mut f, body, Operation::load(span, local.clone()));
        f.set_terminator(body, Terminator::goto(span, header));
        let loaded = append_result(&mut f, exit, Operation::load(span, local));
        append(
            &mut f,
            exit,
            Operation::store(span, loaded, Value::Parameter(ret)),
        );
        terminate_return(&mut f, exit, span);

        verify(f);
    }

    /// Block order is not a definition order: a place may be defined in a higher-numbered block
    /// than the `load` reading it, as long as it dominates that read. The verifier takes a `load`'s
    /// result role from its operand, so it must resolve that role on demand rather than assume the
    /// walk has already reached the definition.
    #[test]
    fn accepts_a_load_whose_place_is_defined_in_a_later_block() {
        let span = Location::new_synthesized();
        let session = CompilerSession::new();
        let env = session.module_env();
        let mut f = FunctionBuilder::new("late_place_definition".into(), Default::default());
        let value = f.add_constant(int_type(), LiteralValue::new_native(42isize), &env);
        let ret = f.add_parameter(int_type(), ParameterKind::Return);
        let entry = f.add_block();
        // Added before the block that defines the place it reads, so that it holds the lower index.
        let using = f.add_block();
        let defining = f.add_block();

        f.set_terminator(entry, Terminator::goto(span, defining));
        let local = append_result(&mut f, defining, Operation::alloca(span, int_type()));
        append(
            &mut f,
            defining,
            Operation::store(span, Value::Constant(value), local.clone()),
        );
        f.set_terminator(defining, Terminator::goto(span, using));
        let loaded = append_result(&mut f, using, Operation::load(span, local));
        append(
            &mut f,
            using,
            Operation::store(span, loaded, Value::Parameter(ret)),
        );
        terminate_return(&mut f, using, span);

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
                Value::Function(callee),
                [Value::Parameter(dictionary)],
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
        let argument = append_result(&mut f, block, Operation::alloca(span, bool_type()));
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
                bool_type(),
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
    #[should_panic(expected = "frame exits with live owned register")]
    fn rejects_unconsumed_owned_register() {
        let span = Location::new_synthesized();
        let mut f = FunctionBuilder::new("bad_register_lifetime".into(), Default::default());
        let block = f.add_block();
        append(
            &mut f,
            block,
            Operation::variant(
                span,
                ustr("A"),
                managed_variant_ty(),
                string_type(),
                Some(VariantPayloadStorage::Inline),
                None,
                None,
            ),
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
            Operation::variant(
                span,
                ustr("A"),
                variant_ty,
                string_type(),
                Some(VariantPayloadStorage::Inline),
                None,
                None,
            ),
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
    fn stack_marker_liveness_drops_an_inner_marker_before_its_loop_redefinition() {
        let span = Location::new_synthesized();
        let session = CompilerSession::new();
        let env = session.module_env();
        let mut f = FunctionBuilder::new("loop_stack_markers".into(), Default::default());
        let entry = f.add_block();
        let loop_header = f.add_block();
        let restore = f.add_block();

        let outer = append_result(&mut f, entry, Operation::stack_save(span));
        f.set_terminator(entry, Terminator::goto(span, loop_header));
        let inner = append_result(&mut f, loop_header, Operation::stack_save(span));
        f.set_terminator(loop_header, Terminator::goto(span, restore));
        append(
            &mut f,
            restore,
            Operation::stack_restore(span, inner.clone()),
        );
        append(
            &mut f,
            restore,
            Operation::stack_restore(span, outer.clone()),
        );
        f.set_terminator(restore, Terminator::goto(span, loop_header));

        let function = f.finish_unverified();
        let mut verifier = Verifier::new(&function, env);
        verifier.verify_structure();
        let live_in = verifier
            .stack_marker_live_in()
            .expect("function has markers");
        let marker = |value| match value {
            Value::Register(marker) => marker,
            _ => unreachable!("stack_save defines a register"),
        };
        let live_at = |block| &live_in[verifier.node_index[&verifier.block_first[&block]]];

        assert_eq!(live_at(loop_header).len(), 1);
        assert!(live_at(loop_header).contains(&marker(outer)));
        assert!(!live_at(loop_header).contains(&marker(inner.clone())));
        assert!(live_at(restore).contains(&marker(inner)));
    }

    #[test]
    fn storage_verifier_does_not_retain_dead_marker_histories_around_a_loop() {
        let span = Location::new_synthesized();
        let session = CompilerSession::new();
        let env = session.module_env();
        let mut f = FunctionBuilder::new("loop_marker_histories".into(), Default::default());
        let condition = f.add_constant(bool_type(), LiteralValue::new_native(true), &env);
        let entry = f.add_block();
        let choose_first = f.add_block();
        let allocate_first = f.add_block();
        let skip_first = f.add_block();
        let choose_second = f.add_block();
        let allocate_second = f.add_block();
        let skip_second = f.add_block();
        let save_inner = f.add_block();
        let restore = f.add_block();

        let outer = append_result(&mut f, entry, Operation::stack_save(span));
        f.set_terminator(entry, Terminator::goto(span, choose_first));
        f.set_terminator(
            choose_first,
            Terminator::cond_br(span, Value::Constant(condition), allocate_first, skip_first),
        );
        append(&mut f, allocate_first, Operation::alloca(span, int_type()));
        f.set_terminator(allocate_first, Terminator::goto(span, choose_second));
        f.set_terminator(skip_first, Terminator::goto(span, choose_second));
        f.set_terminator(
            choose_second,
            Terminator::cond_br(
                span,
                Value::Constant(condition),
                allocate_second,
                skip_second,
            ),
        );
        append(&mut f, allocate_second, Operation::alloca(span, int_type()));
        f.set_terminator(allocate_second, Terminator::goto(span, save_inner));
        f.set_terminator(skip_second, Terminator::goto(span, save_inner));
        let inner = append_result(&mut f, save_inner, Operation::stack_save(span));
        f.set_terminator(save_inner, Terminator::goto(span, restore));
        append(&mut f, restore, Operation::stack_restore(span, inner));
        append(&mut f, restore, Operation::stack_restore(span, outer));
        f.set_terminator(restore, Terminator::goto(span, choose_first));

        let function = f.finish_unverified();
        let mut verifier = Verifier::new(&function, env);
        verifier.verify_structure();
        verifier.collect_value_information(None);
        verifier.collect_storage_roots();
        let max_alternatives = verifier.verify_storage_ownership_max_alternatives();

        // The two independent branches need four live frontier states. If the dead inner marker
        // snapshot survives the backedge, those histories cross with the next iteration's
        // frontiers and this rises beyond four.
        assert_eq!(max_alternatives, 4);
    }

    #[test]
    fn a_runtime_allocation_can_be_consumed_by_pointer_only_deallocation() {
        let span = Location::new_synthesized();
        let session = CompilerSession::new();
        let env = session.module_env();
        let mut f = FunctionBuilder::new("runtime_allocation".into(), Default::default());
        let size = f.add_constant(int_type(), LiteralValue::new_native(24isize), &env);
        let align = f.add_constant(int_type(), LiteralValue::new_native(8isize), &env);
        let block = f.add_block();
        let allocation = append_result(
            &mut f,
            block,
            Operation::runtime_alloc(
                span,
                int_type(),
                Value::Constant(size),
                Value::Constant(align),
            ),
        );
        append(&mut f, block, Operation::runtime_dealloc(span, allocation));
        terminate_return(&mut f, block, span);
        f.finish(env);
    }

    #[test]
    fn a_runtime_allocation_can_be_consumed_differently_on_exclusive_paths() {
        let span = Location::new_synthesized();
        let session = CompilerSession::new();
        let env = session.module_env();
        let mut f =
            FunctionBuilder::new("conditional_runtime_ownership".into(), Default::default());
        let size = f.add_constant(int_type(), LiteralValue::new_native(24isize), &env);
        let align = f.add_constant(int_type(), LiteralValue::new_native(8isize), &env);
        let condition = f.add_constant(bool_type(), LiteralValue::new_native(true), &env);
        let entry = f.add_block();
        let deallocate = f.add_block();
        let transfer = f.add_block();
        let allocation = append_result(
            &mut f,
            entry,
            Operation::runtime_alloc(
                span,
                int_type(),
                Value::Constant(size),
                Value::Constant(align),
            ),
        );
        let owner = append_result(&mut f, entry, Operation::alloca_place(span, int_type()));
        f.set_terminator(
            entry,
            Terminator::cond_br(span, Value::Constant(condition), deallocate, transfer),
        );
        append(
            &mut f,
            deallocate,
            Operation::runtime_dealloc(span, allocation.clone()),
        );
        terminate_return(&mut f, deallocate, span);
        append(&mut f, transfer, Operation::store(span, allocation, owner));
        terminate_return(&mut f, transfer, span);
        f.finish(env);
    }

    #[test]
    #[should_panic(expected = "frame exits with live owned register")]
    fn every_returning_path_must_consume_a_runtime_allocation() {
        let span = Location::new_synthesized();
        let session = CompilerSession::new();
        let env = session.module_env();
        let mut f = FunctionBuilder::new("conditional_runtime_leak".into(), Default::default());
        let size = f.add_constant(int_type(), LiteralValue::new_native(8isize), &env);
        let align = f.add_constant(int_type(), LiteralValue::new_native(8isize), &env);
        let condition = f.add_constant(bool_type(), LiteralValue::new_native(true), &env);
        let entry = f.add_block();
        let deallocate = f.add_block();
        let leak = f.add_block();
        let join = f.add_block();
        let allocation = append_result(
            &mut f,
            entry,
            Operation::runtime_alloc(
                span,
                int_type(),
                Value::Constant(size),
                Value::Constant(align),
            ),
        );
        f.set_terminator(
            entry,
            Terminator::cond_br(span, Value::Constant(condition), deallocate, leak),
        );
        append(
            &mut f,
            deallocate,
            Operation::runtime_dealloc(span, allocation),
        );
        f.set_terminator(deallocate, Terminator::goto(span, join));
        f.set_terminator(leak, Terminator::goto(span, join));
        terminate_return(&mut f, join, span);
        f.finish(env);
    }

    #[test]
    #[should_panic(expected = "use of owned register")]
    fn an_owned_register_cannot_be_used_after_consumption() {
        let span = Location::new_synthesized();
        let session = CompilerSession::new();
        let env = session.module_env();
        let mut f =
            FunctionBuilder::new("use_after_runtime_deallocation".into(), Default::default());
        let size = f.add_constant(int_type(), LiteralValue::new_native(8isize), &env);
        let align = f.add_constant(int_type(), LiteralValue::new_native(8isize), &env);
        let block = f.add_block();
        let allocation = append_result(
            &mut f,
            block,
            Operation::runtime_alloc(
                span,
                int_type(),
                Value::Constant(size),
                Value::Constant(align),
            ),
        );
        append(
            &mut f,
            block,
            Operation::runtime_dealloc(span, allocation.clone()),
        );
        append_result(&mut f, block, Operation::load(span, allocation));
        terminate_return(&mut f, block, span);
        f.finish(env);
    }

    #[test]
    #[should_panic(expected = "owned register")]
    fn a_runtime_allocation_must_be_transferred_or_deallocated() {
        let span = Location::new_synthesized();
        let session = CompilerSession::new();
        let env = session.module_env();
        let mut f = FunctionBuilder::new("leaked_runtime_allocation".into(), Default::default());
        let size = f.add_constant(int_type(), LiteralValue::new_native(8isize), &env);
        let align = f.add_constant(int_type(), LiteralValue::new_native(8isize), &env);
        let block = f.add_block();
        append_result(
            &mut f,
            block,
            Operation::runtime_alloc(
                span,
                int_type(),
                Value::Constant(size),
                Value::Constant(align),
            ),
        );
        terminate_return(&mut f, block, span);
        f.finish(env);
    }

    #[test]
    #[should_panic(expected = "requires a materialized allocation pointer")]
    fn runtime_deallocation_rejects_the_address_of_a_pointer_slot() {
        let span = Location::new_synthesized();
        let mut f = FunctionBuilder::new("deallocate_pointer_slot".into(), Default::default());
        let block = f.add_block();
        let slot = append_result(&mut f, block, Operation::alloca_place(span, int_type()));
        append(&mut f, block, Operation::runtime_dealloc(span, slot));
        terminate_return(&mut f, block, span);
        verify(f);
    }

    #[test]
    #[should_panic(expected = "requires a materialized allocation pointer")]
    fn runtime_deallocation_rejects_stack_storage() {
        let span = Location::new_synthesized();
        let mut f = FunctionBuilder::new("deallocate_stack_storage".into(), Default::default());
        let block = f.add_block();
        let slot = append_result(&mut f, block, Operation::alloca(span, int_type()));
        append(&mut f, block, Operation::runtime_dealloc(span, slot));
        terminate_return(&mut f, block, span);
        verify(f);
    }

    #[test]
    #[should_panic(expected = "runtime_alloc operand 0 must be a materialized int")]
    fn runtime_allocation_rejects_a_non_integer_extent() {
        let span = Location::new_synthesized();
        let session = CompilerSession::new();
        let env = session.module_env();
        let mut f = FunctionBuilder::new("invalid_runtime_extent".into(), Default::default());
        let size = f.add_constant(bool_type(), LiteralValue::new_native(true), &env);
        let align = f.add_constant(int_type(), LiteralValue::new_native(1isize), &env);
        let block = f.add_block();
        let allocation = append_result(
            &mut f,
            block,
            Operation::runtime_alloc(
                span,
                Type::unit(),
                Value::Constant(size),
                Value::Constant(align),
            ),
        );
        append(&mut f, block, Operation::runtime_dealloc(span, allocation));
        terminate_return(&mut f, block, span);
        f.finish(env);
    }

    #[test]
    fn permits_stack_save_after_conditional_allocation() {
        let span = Location::new_synthesized();
        let session = CompilerSession::new();
        let env = session.module_env();
        let mut f = FunctionBuilder::new("conditional_stack_allocation".into(), Default::default());
        let condition = f.add_constant(bool_type(), LiteralValue::new_native(true), &env);
        let entry = f.add_block();
        let allocated = f.add_block();
        let skipped = f.add_block();
        let join = f.add_block();

        f.set_terminator(
            entry,
            Terminator::cond_br(span, Value::Constant(condition), allocated, skipped),
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
            Operation::variant(
                span,
                ustr("A"),
                variant_ty,
                string_type(),
                Some(VariantPayloadStorage::Inline),
                None,
                None,
            ),
        );
        append(&mut f, block, Operation::store(span, value, local.clone()));
        append(&mut f, block, Operation::clear(span, local));
        terminate_return(&mut f, block, span);
        verify(f);
    }

    #[test]
    #[should_panic(expected = "frame exits without consuming owned parameter")]
    fn rejects_an_unconsumed_owned_parameter() {
        let span = Location::new_synthesized();
        let mut f = FunctionBuilder::new("bad_owned_parameter".into(), Default::default());
        f.add_parameter(int_type(), ParameterKind::Owned);
        let block = f.add_block();
        terminate_return(&mut f, block, span);
        verify(f);
    }

    #[test]
    fn an_owned_parameter_may_be_moved_to_the_return_slot() {
        let span = Location::new_synthesized();
        let mut f = FunctionBuilder::new("owned_parameter".into(), Default::default());
        let source = f.add_parameter(int_type(), ParameterKind::Owned);
        let destination = f.add_parameter(int_type(), ParameterKind::Return);
        let block = f.add_block();
        append(
            &mut f,
            block,
            Operation::move_value(
                span,
                Value::Parameter(source),
                Value::Parameter(destination),
            ),
        );
        terminate_return(&mut f, block, span);
        verify(f);
    }
}
