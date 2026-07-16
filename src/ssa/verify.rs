//! Derived structural and ownership verification for SSA functions.
//!
//! The verifier deliberately keeps initialization/drop state out of [`Function`]. SSA operations
//! (`store`, `move`, `drop`, `clear`, …) are the source of truth; this module derives their effects
//! per function and checks them before execution. A later backend may lower the same abstract state
//! to concrete drop flags without exposing those flags to optimization-oriented SSA.

use std::collections::VecDeque;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    Modules,
    format::FormatWith,
    module::{Module, ModuleEnv, id::Id},
    ssa::{
        self, BlockId, Function, InstructionId, InstructionKind, InstructionResult, ParameterTag,
    },
    types::{
        trait_solver::TraitSolverProbe,
        r#type::{Type, TypeKind},
    },
};

/// Verifies all machine-checkable per-function SSA contracts.
///
/// This is intentionally intraprocedural: calls are checked through the uniform by-pointer boundary
/// contract, so lazy lowering does not force the callee's SSA body to exist.
pub(crate) fn verify_function(func: &Function, module: &Module, others: &Modules) {
    let env = ModuleEnv::new(module, others);
    let solver = TraitSolverProbe::from_module(module, others);
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
enum SsaType {
    Lowered(Type),
    Pointer(Box<SsaType>),
}

impl SsaType {
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
    Materialized(SsaType),
    Place(SsaType),
    Dictionary,
    Subscript,
    Function,
    Pattern,
    StackMarker,
}

impl ValueRole {
    fn is_place_operand(&self) -> bool {
        matches!(
            self,
            Self::Place(_) | Self::Materialized(SsaType::Pointer(_))
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
    markers: FxHashMap<ssa::Value, Vec<bool>>,
}

impl AnalysisState {
    fn has_same_allocation_frontier(&self, other: &Self) -> bool {
        self.roots.iter().zip(&other.roots).all(|(left, right)| {
            left.state.may_be_unallocated() == right.state.may_be_unallocated()
        })
    }

    fn join_roots(&mut self, other: &Self, func: &Function, env: &ModuleEnv<'_>) -> bool {
        debug_assert_eq!(self.markers, other.markers);
        debug_assert!(self.has_same_allocation_frontier(other));
        let mut changed = false;
        for (index, (root, other)) in self.roots.iter_mut().zip(&other.roots).enumerate() {
            let mut path = Vec::new();
            if let Some((left, right)) = root.shape_mismatch(other, &mut path) {
                panic!(
                    "SSA function `{}`: storage root {index} has incompatible types at path \
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
    Unwind,
}

struct RootInfo {
    value: ssa::Value,
    ty: Type,
    /// Whether every ownership-relevant subplace of this root is represented precisely by
    /// `StorageState`. Opaque native/custom/variant interiors are still checked at individual
    /// operations, but cannot prove whole-frame absence at exit.
    exact: bool,
}

struct Verifier<'a> {
    func: &'a Function,
    env: ModuleEnv<'a>,
    solver: TraitSolverProbe<'a>,
    instructions: Vec<InstructionId>,
    instruction_index: FxHashMap<InstructionId, usize>,
    instruction_block: FxHashMap<InstructionId, BlockId>,
    block_first: FxHashMap<BlockId, InstructionId>,
    value_roles: FxHashMap<ssa::Value, ValueRole>,
    roots: Vec<RootInfo>,
    root_index: FxHashMap<ssa::Value, usize>,
    trivial_copy: FxHashMap<Type, bool>,
}

impl<'a> Verifier<'a> {
    fn new(func: &'a Function, env: ModuleEnv<'a>, solver: TraitSolverProbe<'a>) -> Self {
        Self {
            func,
            env,
            solver,
            instructions: vec![],
            instruction_index: FxHashMap::default(),
            instruction_block: FxHashMap::default(),
            block_first: FxHashMap::default(),
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
        self.verify_register_consumption();
        self.verify_storage_ownership();
    }

    fn verify_structure(&mut self) {
        let block_ids: Vec<BlockId> = self.func.blocks().collect();
        let non_empty = |b: BlockId| !self.func.block(b).is_empty();
        let target_ok = |b: BlockId| block_ids.contains(&b) && non_empty(b);

        assert!(
            non_empty(self.func.entry()),
            "SSA function `{}`: the entry block is empty",
            self.func.name
        );

        for (instruction, target) in self.func.implicit_unwind_targets() {
            assert!(
                self.func.at(instruction).may_raise_implicitly(),
                "SSA function `{}`: instruction {} has an implicit unwind target but cannot raise \
                 implicitly",
                self.func.name,
                instruction.raw()
            );
            assert!(
                target_ok(target),
                "SSA function `{}`: instruction {} has a missing or empty implicit unwind target",
                self.func.name,
                instruction.raw()
            );
        }

        for &block in &block_ids {
            let instructions: Vec<_> = self.func.block(block).instructions().collect();
            assert!(
                !instructions.is_empty(),
                "SSA function `{}` block {}: a block must not be empty",
                self.func.name,
                block.raw()
            );
            self.block_first.insert(block, instructions[0]);
            let last = instructions.len() - 1;
            for (offset, &instruction) in instructions.iter().enumerate() {
                let whole = self.func.at(instruction);
                whole.verify();
                assert_eq!(
                    whole.is_terminator(),
                    offset == last,
                    "SSA function `{}` block {}: a terminator must be the block's last instruction \
                     and appear exactly once",
                    self.func.name,
                    block.raw()
                );
                self.instruction_index
                    .insert(instruction, self.instructions.len());
                self.instruction_block.insert(instruction, block);
                self.instructions.push(instruction);
            }

            match &self.func.at(instructions[last]).kind {
                InstructionKind::ConditionalBranch {
                    on_success,
                    on_failure,
                } => assert!(
                    target_ok(*on_success) && target_ok(*on_failure),
                    "SSA function `{}` block {}: condbr targets a missing or empty block",
                    self.func.name,
                    block.raw()
                ),
                InstructionKind::UnconditionalBranch { target } => assert!(
                    target_ok(*target),
                    "SSA function `{}` block {}: br targets a missing or empty block",
                    self.func.name,
                    block.raw()
                ),
                InstructionKind::Invoke { normal, unwind } => assert!(
                    target_ok(*normal) && target_ok(*unwind),
                    "SSA function `{}` block {}: invoke targets a missing or empty block",
                    self.func.name,
                    block.raw()
                ),
                InstructionKind::CheckCallDepth {
                    successors: Some((normal, unwind)),
                }
                | InstructionKind::CheckFuel {
                    successors: Some((normal, unwind)),
                } => assert!(
                    target_ok(*normal) && target_ok(*unwind),
                    "SSA function `{}` block {}: runtime check targets a missing or empty block",
                    self.func.name,
                    block.raw()
                ),
                _ => {}
            }
        }
    }

    fn collect_value_information(&mut self) {
        for (index, parameter) in self.func.parameters().iter().enumerate() {
            let value = ssa::Value::Parameter(ssa::ParameterId::from_index(index));
            let role = match parameter.tag {
                ParameterTag::Dictionary => ValueRole::Dictionary,
                ParameterTag::Parameter(_) => ValueRole::Place(SsaType::Lowered(parameter.type_)),
                ParameterTag::Return if self.func.result_convention().returns_place() => {
                    ValueRole::Place(SsaType::Pointer(Box::new(SsaType::Lowered(
                        parameter.type_,
                    ))))
                }
                ParameterTag::Return => ValueRole::Place(SsaType::Lowered(parameter.type_)),
            };
            self.value_roles.insert(value, role);
        }

        for index in 0..self.instructions.len() {
            let instruction = self.instructions[index];
            let Some(value) = self.func.definition(instruction) else {
                continue;
            };
            let role = self.resolve_result(self.func.at(instruction).result());
            if let InstructionKind::Alloca { ty } = self.func.at(instruction).kind {
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

    fn resolve_result(&self, result: InstructionResult) -> ValueRole {
        match result {
            InstructionResult::Lowered(ty) => ValueRole::Materialized(SsaType::Lowered(ty)),
            InstructionResult::Pointer(pointee) => {
                ValueRole::Place(self.resolve_result_type(*pointee))
            }
            InstructionResult::Pointee(pointer) => match self.resolve_result(*pointer) {
                ValueRole::Place(ty) => ValueRole::Materialized(ty),
                other => panic!(
                    "SSA function `{}`: `Pointee` result refers to non-place role {other:?}",
                    self.func.name
                ),
            },
            InstructionResult::Same(value) => self.role(&value),
            InstructionResult::StackMarker => ValueRole::StackMarker,
            InstructionResult::Nothing => {
                panic!(
                    "SSA function `{}`: result-less instruction was defined",
                    self.func.name
                )
            }
        }
    }

    fn resolve_result_type(&self, result: InstructionResult) -> SsaType {
        match result {
            InstructionResult::Lowered(ty) => SsaType::Lowered(ty),
            InstructionResult::Pointer(inner) => {
                SsaType::Pointer(Box::new(self.resolve_result_type(*inner)))
            }
            InstructionResult::Same(value) => match self.role(&value) {
                ValueRole::Materialized(ty) | ValueRole::Place(ty) => ty.clone(),
                other => panic!(
                    "SSA function `{}`: type requested for non-typed role {other:?}",
                    self.func.name
                ),
            },
            InstructionResult::Pointee(pointer) => match self.resolve_result(*pointer) {
                ValueRole::Place(ty) => ty,
                other => panic!(
                    "SSA function `{}`: pointee type requested from {other:?}",
                    self.func.name
                ),
            },
            InstructionResult::StackMarker | InstructionResult::Nothing => panic!(
                "SSA function `{}`: non-value result used as a value type",
                self.func.name
            ),
        }
    }

    fn role(&self, value: &ssa::Value) -> ValueRole {
        match value {
            ssa::Value::Constant(id) => {
                ValueRole::Materialized(SsaType::Lowered(self.func.constant(*id).ty))
            }
            ssa::Value::Dictionary(_) => ValueRole::Dictionary,
            ssa::Value::Subscript(_) => ValueRole::Subscript,
            ssa::Value::Function(_) => ValueRole::Function,
            ssa::Value::Pattern(_) => ValueRole::Pattern,
            ssa::Value::Parameter(_) | ssa::Value::Register(_) => self
                .value_roles
                .get(value)
                .unwrap_or_else(|| {
                    panic!(
                        "SSA function `{}`: undefined operand {value}",
                        self.func.name
                    )
                })
                .clone(),
        }
    }

    fn materialized_type(&self, value: &ssa::Value) -> Option<SsaType> {
        match value {
            ssa::Value::Constant(id) => Some(SsaType::Lowered(self.func.constant(*id).ty)),
            _ => match self.role(value) {
                ValueRole::Materialized(ty) => Some(ty),
                ValueRole::Function | ValueRole::Subscript => None,
                _ => None,
            },
        }
    }

    fn verify_operand_roles_and_dominance(&self) {
        let dominators = self.compute_instruction_dominators();
        for &instruction in &self.instructions {
            let whole = self.func.at(instruction);
            for operand in whole.operands.iter() {
                if let ssa::Value::Register(definition) = operand {
                    let def_block = self.instruction_block[definition];
                    let use_block = self.instruction_block[&instruction];
                    let dominates = match dominators.get(&instruction) {
                        Some(dominators) => dominators.contains(definition),
                        // Unreachable instructions are not part of the dominance fixed point. Still
                        // reject a use preceding its definition within one unreachable block; no
                        // meaningful cross-block dominance relation exists without a path from the
                        // entry.
                        None if def_block == use_block => {
                            self.instruction_index[definition]
                                < self.instruction_index[&instruction]
                        }
                        None => true,
                    };
                    assert!(
                        dominates,
                        "SSA function `{}`: operand {operand} from block {} does not dominate \
                         instruction {} in block {}\n{}",
                        self.func.name,
                        def_block.raw(),
                        instruction.raw(),
                        use_block.raw(),
                        self.func.format_with(&self.env)
                    );
                }
            }
            self.verify_instruction_roles(instruction);
        }
    }

    fn verify_instruction_roles(&self, instruction: InstructionId) {
        let whole = self.func.at(instruction);
        let operands = &whole.operands;
        let place = |index: usize| {
            assert!(
                self.role(&operands[index]).is_place_operand(),
                "SSA function `{}` instruction {}: operand {} must be a place, got {:?}",
                self.func.name,
                instruction.raw(),
                index,
                self.role(&operands[index])
            );
        };
        let value = |index: usize| {
            assert!(
                self.materialized_type(&operands[index]).is_some()
                    || self.role(&operands[index]).is_materialized(),
                "SSA function `{}` instruction {}: operand {} must be a materialized value, got {:?}",
                self.func.name,
                instruction.raw(),
                index,
                self.role(&operands[index])
            );
        };
        let evidence = |index: usize| {
            assert!(
                self.role(&operands[index]).is_evidence(),
                "SSA function `{}` instruction {}: operand {} must be evidence, got {:?}",
                self.func.name,
                instruction.raw(),
                index,
                self.role(&operands[index])
            );
        };

        match &whole.kind {
            InstructionKind::Alloca { .. } => {
                if !operands.is_empty() {
                    evidence(0);
                }
            }
            InstructionKind::AllocaPlace { .. }
            | InstructionKind::Resume
            | InstructionKind::Ret
            | InstructionKind::Variant { .. }
            | InstructionKind::StackSave
            | InstructionKind::CheckCallDepth { .. }
            | InstructionKind::CheckFuel { .. } => {}
            InstructionKind::Call | InstructionKind::Invoke { .. } => {
                assert!(
                    matches!(
                        self.role(&operands[0]),
                        ValueRole::Function | ValueRole::Place(_)
                    ),
                    "SSA function `{}` instruction {}: callee must be a function or function place",
                    self.func.name,
                    instruction.raw()
                );
                for index in 1..operands.len() - 1 {
                    assert!(
                        self.role(&operands[index]).is_place_operand()
                            || self.role(&operands[index]).is_evidence(),
                        "SSA function `{}` instruction {}: call operand {} must be a place or evidence",
                        self.func.name,
                        instruction.raw(),
                        index
                    );
                }
                assert!(
                    self.role(operands.last().unwrap()).is_place_operand(),
                    "SSA function `{}` instruction {}: the trailing call result operand must be a \
                     place",
                    self.func.name,
                    instruction.raw()
                );
            }
            InstructionKind::Project { .. } => {
                assert!(
                    matches!(
                        self.role(&operands[0]),
                        ValueRole::Function | ValueRole::Place(_)
                    ),
                    "SSA function `{}` instruction {}: callee must be a function or function place",
                    self.func.name,
                    instruction.raw()
                );
                for index in 1..operands.len() {
                    assert!(
                        self.role(&operands[index]).is_place_operand()
                            || self.role(&operands[index]).is_evidence(),
                        "SSA function `{}` instruction {}: project operand {} must be a place or \
                         evidence",
                        self.func.name,
                        instruction.raw(),
                        index
                    );
                }
            }
            InstructionKind::Yield
            | InstructionKind::EndProject
            | InstructionKind::ExtractTag
            | InstructionKind::Clear
            | InstructionKind::DropClosureEnv
            | InstructionKind::CloneClosureEnv { .. } => place(0),
            InstructionKind::CompareEqual => {
                assert!(
                    self.role(&operands[0]).is_place_operand()
                        || self.materialized_type(&operands[0]).is_some(),
                    "SSA function `{}` instruction {}: comparison scrutinee must be a place or value",
                    self.func.name,
                    instruction.raw()
                );
                assert!(
                    matches!(self.role(&operands[1]), ValueRole::Pattern),
                    "SSA function `{}` instruction {}: comparison pattern must be compile-time data",
                    self.func.name,
                    instruction.raw()
                );
            }
            InstructionKind::ConditionalBranch { .. } => value(0),
            InstructionKind::UnconditionalBranch { .. } => {}
            InstructionKind::Load => place(0),
            InstructionKind::Subfield { .. } => {
                place(0);
                value(1);
            }
            InstructionKind::DictEntry { .. } => evidence(0),
            InstructionKind::SubscriptMember { .. } => evidence(0),
            InstructionKind::BuildSubscript { .. } => {
                for index in 0..operands.len() {
                    evidence(index);
                }
            }
            InstructionKind::Store => {
                assert!(
                    self.materialized_type(&operands[0]).is_some()
                        || self.role(&operands[0]).is_place_operand()
                        || self.role(&operands[0]).is_materialized(),
                    "SSA function `{}` instruction {}: stored operand must be a value or place pointer",
                    self.func.name,
                    instruction.raw()
                );
                place(1);
                if let (Some(value_ty), Some(destination_ty)) = (
                    self.materialized_type(&operands[0]),
                    self.place_pointee_type(&operands[1]),
                ) {
                    assert!(
                        value_ty.representation_compatible(&destination_ty, &self.env),
                        "SSA function `{}` instruction {}: stored value type {} differs from \
                         destination type {}\n{}",
                        self.func.name,
                        instruction.raw(),
                        value_ty.format(&self.env),
                        destination_ty.format(&self.env),
                        self.func.format_with(&self.env)
                    );
                }
            }
            InstructionKind::Memcpy | InstructionKind::Move => {
                place(0);
                place(1);
                if let (Some(source_ty), Some(destination_ty)) = (
                    self.place_pointee_type(&operands[0]),
                    self.place_pointee_type(&operands[1]),
                ) {
                    // A witnessed dynamic move may connect distinct generic descriptors whose
                    // equality was established by HIR inference but is not retained in the lowered
                    // SSA signature. The witness supplies the runtime layout; making this check
                    // fully standalone requires explicit normalized-layout/equality metadata.
                    assert!(
                        operands.len() == 3
                            || source_ty.representation_compatible(&destination_ty, &self.env),
                        "SSA function `{}` instruction {}: source pointee type {} differs from \
                         destination pointee type {}\n{}",
                        self.func.name,
                        instruction.raw(),
                        source_ty.format(&self.env),
                        destination_ty.format(&self.env),
                        self.func.format_with(&self.env)
                    );
                }
                if operands.len() == 3 {
                    evidence(2);
                }
            }
            InstructionKind::StackRestore => assert!(
                matches!(self.role(&operands[0]), ValueRole::StackMarker),
                "SSA function `{}` instruction {}: stack_restore needs a stack marker",
                self.func.name,
                instruction.raw()
            ),
            InstructionKind::Drop => {
                place(0);
                assert!(
                    matches!(
                        self.role(&operands[1]),
                        ValueRole::Function | ValueRole::Place(_)
                    ),
                    "SSA function `{}` instruction {}: drop callee must be a function or function place",
                    self.func.name,
                    instruction.raw()
                );
            }
            InstructionKind::BuildClosure {
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

    fn compute_instruction_dominators(&self) -> FxHashMap<InstructionId, FxHashSet<InstructionId>> {
        let entry = self.block_first[&self.func.entry()];
        let mut reachable = FxHashSet::default();
        let mut predecessors: FxHashMap<InstructionId, Vec<InstructionId>> = FxHashMap::default();
        let mut worklist = VecDeque::from([entry]);
        reachable.insert(entry);
        while let Some(instruction) = worklist.pop_front() {
            for (successor, _) in self.successors(instruction) {
                let incoming = predecessors.entry(successor).or_default();
                if !incoming.contains(&instruction) {
                    incoming.push(instruction);
                }
                if reachable.insert(successor) {
                    worklist.push_back(successor);
                }
            }
        }

        // Dominance is defined over the instruction CFG, not merely blocks: an implicit unwind edge
        // can leave in the middle of a block, so definitions later in that block do not dominate the
        // landing pad.
        let all_reachable = reachable.clone();
        let mut result: FxHashMap<InstructionId, FxHashSet<InstructionId>> = FxHashMap::default();
        for &instruction in &reachable {
            result.insert(
                instruction,
                if instruction == entry {
                    FxHashSet::from_iter([entry])
                } else {
                    all_reachable.clone()
                },
            );
        }
        loop {
            let mut changed = false;
            for &instruction in &reachable {
                if instruction == entry {
                    continue;
                }
                let incoming = &predecessors[&instruction];
                let (first, rest) = incoming
                    .split_first()
                    .expect("a reachable non-entry instruction must have a predecessor");
                let mut new = result[first].clone();
                new.retain(|candidate| {
                    rest.iter()
                        .all(|predecessor| result[predecessor].contains(candidate))
                });
                new.insert(instruction);
                if new != result[&instruction] {
                    result.insert(instruction, new);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        result
    }

    fn place_pointee_type(&self, value: &ssa::Value) -> Option<SsaType> {
        match self.role(value) {
            ValueRole::Place(ty) => Some(ty),
            ValueRole::Materialized(SsaType::Pointer(ty)) => Some(*ty),
            _ => None,
        }
    }

    fn verify_register_consumption(&mut self) {
        let mut consuming_uses: FxHashMap<ssa::Value, usize> = FxHashMap::default();
        for &instruction in &self.instructions {
            let whole = self.func.at(instruction);
            for (index, operand) in whole.operands.iter().enumerate() {
                if self.operand_consumes_value(whole, index) {
                    *consuming_uses.entry(operand.clone()).or_default() += 1;
                }
            }
        }
        for &instruction in &self.instructions {
            let Some(value) = self.func.definition(instruction) else {
                continue;
            };
            if self.register_needs_consuming_use(instruction) {
                assert_eq!(
                    consuming_uses.get(&value).copied().unwrap_or(0),
                    1,
                    "SSA function `{}`: owned register {value} must have exactly one consuming use",
                    self.func.name
                );
            }
        }
    }

    fn operand_consumes_value(&self, instruction: &crate::ssa::Instruction, index: usize) -> bool {
        matches!(instruction.kind, InstructionKind::Store) && index == 0
    }

    fn register_needs_consuming_use(&self, instruction: InstructionId) -> bool {
        match &self.func.at(instruction).kind {
            InstructionKind::Variant { .. } | InstructionKind::CloneClosureEnv { .. } => true,
            InstructionKind::BuildClosure {
                num_hidden_dicts,
                has_env_dict,
                ..
            } => {
                let captures = self.func.at(instruction).operands.len()
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
        };
        // Keep different allocation frontiers and stack-marker snapshots as separate alternatives.
        // Merging either correlation would make it impossible to verify what a later
        // `stack_restore` reclaims. Within one alternative, ordinary ownership states still join to
        // a fixed point.
        let mut inputs: Vec<Vec<AnalysisState>> = vec![vec![]; self.instructions.len()];
        let entry = self.block_first[&self.func.entry()];
        inputs[self.instruction_index[&entry]].push(initial);
        let mut worklist = VecDeque::from([(entry, 0)]);

        while let Some((instruction, alternative)) = worklist.pop_front() {
            let index = self.instruction_index[&instruction];
            let input = inputs[index][alternative].clone();
            let edges = self.transfer(instruction, &input);
            for (target, state) in edges {
                let target_index = self.instruction_index[&target];
                let alternatives = &mut inputs[target_index];
                let (alternative, changed) = match alternatives.iter().position(|existing| {
                    existing.markers == state.markers
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

    fn transfer(
        &mut self,
        instruction: InstructionId,
        input: &AnalysisState,
    ) -> Vec<(InstructionId, AnalysisState)> {
        let whole = self.func.at(instruction);
        let mut normal = input.clone();
        let mut unwind = input.clone();

        match &whole.kind {
            InstructionKind::Alloca { .. } => {
                let root = self.root_index[&self.func.definition(instruction).unwrap()];
                normal.roots[root].set_all(LeafState::ABSENT);
            }
            InstructionKind::AllocaPlace { .. } => {}
            InstructionKind::Store => {
                self.transfer_store(&whole.operands[0], &whole.operands[1], &mut normal);
            }
            InstructionKind::Memcpy => {
                if let Some(SsaType::Lowered(ty)) = self.place_pointee_type(&whole.operands[0]) {
                    assert!(
                        self.is_trivial_copy(ty),
                        "SSA function `{}`: memcpy source type is not TrivialCopy",
                        self.func.name
                    );
                }
                self.transfer_copy_or_move(
                    &whole.operands[0],
                    &whole.operands[1],
                    false,
                    &mut normal,
                );
            }
            InstructionKind::Move => {
                self.transfer_copy_or_move(
                    &whole.operands[0],
                    &whole.operands[1],
                    true,
                    &mut normal,
                );
            }
            InstructionKind::Clear => {
                self.transfer_clear(&whole.operands[0], &mut normal);
            }
            InstructionKind::Drop => {
                self.transfer_drop(&whole.operands[0], &mut normal);
                self.transfer_drop(&whole.operands[0], &mut unwind);
            }
            InstructionKind::Call | InstructionKind::Invoke { .. } => {
                // Instruction arity and role verification establish that every call ends in a
                // result place, including calls returning unit.
                let destination = whole
                    .operands
                    .last()
                    .expect("call arity was verified before ownership analysis");
                self.initialize_call_result(instruction, destination, &mut normal);
            }
            InstructionKind::BuildClosure {
                num_hidden_dicts,
                has_env_dict,
                ..
            } => {
                let captures_end = whole.operands.len() - usize::from(*has_env_dict);
                for capture in &whole.operands[*num_hidden_dicts as usize..captures_end] {
                    self.consume_place(capture, &mut normal);
                }
            }
            InstructionKind::StackSave => {
                let marker = self.func.definition(instruction).unwrap();
                for (index, root) in normal.roots.iter().enumerate() {
                    debug_assert!(
                        root.state.is_definitely_unallocated() || !root.state.may_be_unallocated(),
                        "SSA function `{}` instruction {}: allocation-frontier alternatives were \
                         incorrectly merged before stack_save for {}",
                        self.func.name,
                        instruction.raw(),
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
            InstructionKind::StackRestore => {
                self.transfer_stack_restore(&whole.operands[0], &mut normal);
            }
            InstructionKind::Ret | InstructionKind::Resume => {
                self.verify_frame_exit(instruction, input);
            }
            _ => {}
        }

        let mut result = vec![];
        for (target, edge) in self.successors(instruction) {
            result.push((
                target,
                match edge {
                    EdgeKind::Normal => normal.clone(),
                    EdgeKind::Unwind => unwind.clone(),
                },
            ));
        }
        result
    }

    fn transfer_store(
        &mut self,
        value: &ssa::Value,
        destination: &ssa::Value,
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
            "SSA function `{}`: store overwrites storage with a live semantic drop obligation",
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
        source: &ssa::Value,
        destination: &ssa::Value,
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
                    "SSA function `{}`: {} reads storage that is not definitely initialized \
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
                    "SSA function `{}`: {} overwrites storage with a live semantic drop obligation",
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

    fn transfer_clear(&self, destination: &ssa::Value, state: &mut AnalysisState) {
        let LocalPlace::Root {
            root,
            path: Some(path),
        } = self.local_place(destination)
        else {
            return;
        };
        let target = state.roots[root]
            .at_path(&path)
            .expect("tracked clear path must exist");
        assert!(
            target.state.may_be_overwritten_without_drop(),
            "SSA function `{}`: clear discards a live semantic drop obligation",
            self.func.name
        );
        state.roots[root].set_path_all(&path, LeafState::ABSENT);
    }

    fn transfer_drop(&self, target: &ssa::Value, state: &mut AnalysisState) {
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
            "SSA function `{}`: drop targets storage that may not have been allocated",
            self.func.name
        );
        state.roots[root].set_path_all(&path, LeafState::ABSENT);
    }

    fn consume_place(&self, source: &ssa::Value, state: &mut AnalysisState) {
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
            "SSA function `{}`: closure capture consumes storage that is not definitely initialized",
            self.func.name
        );
        state.roots[root].set_path_all(&path, LeafState::ABSENT);
    }

    fn initialize_call_result(
        &mut self,
        instruction: InstructionId,
        destination: &ssa::Value,
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
            "SSA function `{}` instruction {}: call result overwrites storage with a live semantic \
             drop obligation in {destination} ({target:?})\n{}",
            self.func.name,
            instruction.raw(),
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

    fn transfer_stack_restore(&self, marker: &ssa::Value, state: &mut AnalysisState) {
        // A stack marker is an immutable saved frontier, not a linear value. Lowering may restore
        // the same marker repeatedly after allocating new temporaries at that frontier.
        let snapshot = state.markers.get(marker).cloned().unwrap_or_else(|| {
            panic!(
                "SSA function `{}`: stack_restore uses a marker unavailable on this path",
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
                "SSA function `{}`: stack_restore reclaims storage with a live semantic drop \
                 obligation in {} ({root:?})\n{}",
                self.func.name,
                self.roots[index].value,
                self.func.format_with(&self.env)
            );
            root.set_all(LeafState::UNALLOCATED);
        }
    }

    fn verify_frame_exit(&self, instruction: InstructionId, state: &AnalysisState) {
        for (index, root) in state.roots.iter().enumerate() {
            if !self.roots[index].exact {
                continue;
            }
            assert!(
                !root.state.may_need_drop(),
                "SSA function `{}` instruction {}: frame exits with a live semantic drop \
                 obligation in {}",
                self.func.name,
                instruction.raw(),
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

    fn value_needs_drop(&mut self, value: &ssa::Value) -> bool {
        match value {
            ssa::Value::Constant(_)
            | ssa::Value::Function(_)
            | ssa::Value::Subscript(_)
            | ssa::Value::Dictionary(_)
            | ssa::Value::Pattern(_) => false,
            ssa::Value::Parameter(_) => false,
            ssa::Value::Register(instruction) => match &self.func.at(*instruction).kind {
                InstructionKind::Variant { .. } | InstructionKind::CloneClosureEnv { .. } => true,
                InstructionKind::BuildClosure {
                    num_hidden_dicts,
                    has_env_dict,
                    ..
                } => {
                    self.func.at(*instruction).operands.len()
                        > *num_hidden_dicts as usize + usize::from(*has_env_dict)
                }
                InstructionKind::Load
                | InstructionKind::CompareEqual
                | InstructionKind::ExtractTag
                | InstructionKind::BuildSubscript { .. } => false,
                _ => match self.func.at(*instruction).result() {
                    InstructionResult::Lowered(ty) => !self.is_trivial_copy(ty),
                    _ => false,
                },
            },
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

    fn local_place(&self, value: &ssa::Value) -> LocalPlace {
        let ssa::Value::Register(instruction) = value else {
            return LocalPlace::External;
        };
        match &self.func.at(*instruction).kind {
            InstructionKind::Alloca { .. } => LocalPlace::Root {
                root: self.root_index[value],
                path: Some(vec![]),
            },
            InstructionKind::Subfield { .. } => {
                let base = self.local_place(&self.func.at(*instruction).operands[0]);
                let index = self.static_field_index(&self.func.at(*instruction).operands[1]);
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

    fn static_field_index(&self, value: &ssa::Value) -> Option<usize> {
        let ssa::Value::Constant(id) = value else {
            return None;
        };
        self.func
            .constant(*id)
            .representation
            .as_primitive_ty::<isize>()
            .and_then(|index| usize::try_from(*index).ok())
    }

    fn successors(&self, instruction: InstructionId) -> Vec<(InstructionId, EdgeKind)> {
        let whole = self.func.at(instruction);
        let mut result = vec![];
        let first = |block: &BlockId| self.block_first[block];
        match &whole.kind {
            InstructionKind::ConditionalBranch {
                on_success,
                on_failure,
            } => {
                result.push((first(on_success), EdgeKind::Normal));
                result.push((first(on_failure), EdgeKind::Normal));
            }
            InstructionKind::UnconditionalBranch { target } => {
                result.push((first(target), EdgeKind::Normal));
            }
            InstructionKind::Invoke { normal, unwind } => {
                result.push((first(normal), EdgeKind::Normal));
                result.push((first(unwind), EdgeKind::Unwind));
            }
            InstructionKind::CheckCallDepth {
                successors: Some((normal, unwind)),
            }
            | InstructionKind::CheckFuel {
                successors: Some((normal, unwind)),
            } => {
                result.push((first(normal), EdgeKind::Normal));
                result.push((first(unwind), EdgeKind::Unwind));
            }
            InstructionKind::Ret | InstructionKind::Resume => {}
            _ => {
                let index = self.instruction_index[&instruction];
                let next = self.instructions.get(index + 1).copied().filter(|next| {
                    self.instruction_block[next] == self.instruction_block[&instruction]
                });
                if let Some(next) = next {
                    result.push((next, EdgeKind::Normal));
                }
            }
        }
        if let Some(unwind) = self.func.implicit_unwind_target(instruction) {
            result.push((first(&unwind), EdgeKind::Unwind));
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        CompilerSession, Location,
        hir::value::LiteralValue,
        module::{FunctionId, LocalFunctionId, ModuleId},
        ssa::{Function, Instruction, ParameterTag, verify::verify_function},
        std::math::int_type,
        types::r#type::Type,
    };

    fn verify(f: &Function) {
        let session = CompilerSession::new();
        let env = session.module_env();
        verify_function(f, env.current, env.modules);
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
        let mut f = Function::new("bad_store".into(), Default::default());
        let ret = f.add_parameter(int_type(), ParameterTag::Return);
        let constant = f.add_constant(int_type(), LiteralValue::new_native(0isize), &env);
        let variant_ty = managed_variant_ty();
        let block = f.add_block().id();
        let local = f
            .block_mut(block)
            .append(Instruction::alloca(span, variant_ty));
        let first =
            f.block_mut(block)
                .append(Instruction::variant(span, ustr::ustr("A"), variant_ty));
        f.block_mut(block).append(Instruction::store(
            span,
            crate::ssa::Value::Register(first),
            crate::ssa::Value::Register(local),
        ));
        let second =
            f.block_mut(block)
                .append(Instruction::variant(span, ustr::ustr("A"), variant_ty));
        f.block_mut(block).append(Instruction::store(
            span,
            crate::ssa::Value::Register(second),
            crate::ssa::Value::Register(local),
        ));
        f.block_mut(block).append(Instruction::store(
            span,
            crate::ssa::Value::Constant(constant),
            crate::ssa::Value::Parameter(ret),
        ));
        f.block_mut(block).append(Instruction::ret(span));
        verify(&f);
    }

    #[test]
    #[should_panic(expected = "does not dominate")]
    fn rejects_register_use_not_dominated_by_its_definition() {
        let span = Location::new_synthesized();
        let session = CompilerSession::new();
        let env = session.module_env();
        let mut f = Function::new("bad_dominance".into(), Default::default());
        let condition = f.add_constant(
            crate::std::logic::bool_type(),
            LiteralValue::new_native(true),
            &env,
        );
        let variant_ty = managed_variant_ty();
        let entry = f.add_block().id();
        let defining = f.add_block().id();
        let using = f.add_block().id();
        let local = f
            .block_mut(entry)
            .append(Instruction::alloca(span, variant_ty));
        f.block_mut(entry).append(Instruction::condbr(
            span,
            crate::ssa::Value::Constant(condition),
            defining,
            using,
        ));
        let value =
            f.block_mut(defining)
                .append(Instruction::variant(span, ustr::ustr("A"), variant_ty));
        f.block_mut(defining).append(Instruction::br(span, using));
        f.block_mut(using).append(Instruction::store(
            span,
            crate::ssa::Value::Register(value),
            crate::ssa::Value::Register(local),
        ));
        f.block_mut(using).append(Instruction::ret(span));
        verify(&f);
    }

    #[test]
    #[should_panic(expected = "does not dominate")]
    fn rejects_use_after_an_earlier_instruction_unwinds() {
        let span = Location::new_synthesized();
        let mut f = Function::new("bad_unwind_dominance".into(), Default::default());
        let entry = f.add_block().id();
        let normal = f.add_block().id();
        let unwind = f.add_block().id();

        let raising = f
            .block_mut(entry)
            .append(Instruction::alloca(span, int_type()));
        let late_definition = f
            .block_mut(entry)
            .append(Instruction::alloca(span, int_type()));
        f.block_mut(entry).append(Instruction::br(span, normal));
        f.set_implicit_unwind_target(raising, unwind);

        f.block_mut(normal).append(Instruction::ret(span));
        f.block_mut(unwind).append(Instruction::load(
            span,
            crate::ssa::Value::Register(late_definition),
        ));
        f.block_mut(unwind).append(Instruction::resume(span));
        verify(&f);
    }

    #[test]
    #[should_panic(expected = "trailing call result operand must be a place")]
    fn rejects_call_without_a_trailing_result_place() {
        let span = Location::new_synthesized();
        let mut f = Function::new("bad_call_result".into(), Default::default());
        let dictionary = f.add_parameter(int_type(), ParameterTag::Dictionary);
        let block = f.add_block().id();
        let callee = FunctionId {
            module: ModuleId::default(),
            function: LocalFunctionId::default(),
        };
        f.block_mut(block).append(Instruction::call(
            span,
            crate::ssa::Value::Function(callee),
            [crate::ssa::Value::Parameter(dictionary)],
        ));
        f.block_mut(block).append(Instruction::ret(span));
        verify(&f);
    }

    #[test]
    #[should_panic(expected = "must have exactly one consuming use")]
    fn rejects_unconsumed_owned_register() {
        let span = Location::new_synthesized();
        let mut f = Function::new("bad_register_lifetime".into(), Default::default());
        let block = f.add_block().id();
        f.block_mut(block).append(Instruction::variant(
            span,
            ustr::ustr("A"),
            managed_variant_ty(),
        ));
        f.block_mut(block).append(Instruction::ret(span));
        verify(&f);
    }

    #[test]
    #[should_panic(
        expected = "stack_restore reclaims storage with a live semantic drop obligation"
    )]
    fn rejects_stack_restore_across_live_owned_storage() {
        let span = Location::new_synthesized();
        let mut f = Function::new("bad_stack_restore".into(), Default::default());
        let variant_ty = managed_variant_ty();
        let block = f.add_block().id();
        let marker = f.block_mut(block).append(Instruction::stack_save(span));
        let local = f
            .block_mut(block)
            .append(Instruction::alloca(span, variant_ty));
        let value =
            f.block_mut(block)
                .append(Instruction::variant(span, ustr::ustr("A"), variant_ty));
        f.block_mut(block).append(Instruction::store(
            span,
            crate::ssa::Value::Register(value),
            crate::ssa::Value::Register(local),
        ));
        f.block_mut(block).append(Instruction::stack_restore(
            span,
            crate::ssa::Value::Register(marker),
        ));
        f.block_mut(block).append(Instruction::ret(span));
        verify(&f);
    }

    #[test]
    fn permits_reusing_a_stack_marker() {
        let span = Location::new_synthesized();
        let mut f = Function::new("reused_stack_marker".into(), Default::default());
        let block = f.add_block().id();
        let marker = f.block_mut(block).append(Instruction::stack_save(span));

        f.block_mut(block)
            .append(Instruction::alloca(span, int_type()));
        f.block_mut(block).append(Instruction::stack_restore(
            span,
            crate::ssa::Value::Register(marker),
        ));

        f.block_mut(block)
            .append(Instruction::alloca(span, int_type()));
        f.block_mut(block).append(Instruction::stack_restore(
            span,
            crate::ssa::Value::Register(marker),
        ));
        f.block_mut(block).append(Instruction::ret(span));
        verify(&f);
    }

    #[test]
    fn permits_stack_save_after_conditional_allocation() {
        let span = Location::new_synthesized();
        let session = CompilerSession::new();
        let env = session.module_env();
        let mut f = Function::new("conditional_stack_allocation".into(), Default::default());
        let condition = f.add_constant(
            crate::std::logic::bool_type(),
            LiteralValue::new_native(true),
            &env,
        );
        let entry = f.add_block().id();
        let allocated = f.add_block().id();
        let skipped = f.add_block().id();
        let join = f.add_block().id();

        f.block_mut(entry).append(Instruction::condbr(
            span,
            crate::ssa::Value::Constant(condition),
            allocated,
            skipped,
        ));
        f.block_mut(allocated)
            .append(Instruction::alloca(span, int_type()));
        f.block_mut(allocated).append(Instruction::br(span, join));
        f.block_mut(skipped).append(Instruction::br(span, join));
        f.block_mut(join).append(Instruction::stack_save(span));
        f.block_mut(join).append(Instruction::ret(span));
        verify(&f);
    }

    #[test]
    #[should_panic(expected = "clear discards a live semantic drop obligation")]
    fn rejects_clearing_owned_storage_without_drop() {
        let span = Location::new_synthesized();
        let mut f = Function::new("bad_clear".into(), Default::default());
        let variant_ty = managed_variant_ty();
        let block = f.add_block().id();
        let local = f
            .block_mut(block)
            .append(Instruction::alloca(span, variant_ty));
        let value =
            f.block_mut(block)
                .append(Instruction::variant(span, ustr::ustr("A"), variant_ty));
        f.block_mut(block).append(Instruction::store(
            span,
            crate::ssa::Value::Register(value),
            crate::ssa::Value::Register(local),
        ));
        f.block_mut(block)
            .append(Instruction::clear(span, crate::ssa::Value::Register(local)));
        f.block_mut(block).append(Instruction::ret(span));
        verify(&f);
    }
}
