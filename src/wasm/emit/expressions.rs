// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Shared scalar-storage facts and conservative Wasm expression-tree plans.

use std::cell::OnceCell;

use smallvec::SmallVec;

use crate::{
    CompilerSession, FxHashMap, FxHashSet, define_id_type,
    mir::{
        BasicBlock, BlockId, Function, Operation, OperationKind, ParameterId, ParameterKind, Value,
        ValueId,
        dominance::Dominance,
        pass::known_callee::KnownCallee,
        physical::program::ResolvedPhysicalProgram,
        role::{MirType, ValueRole, ValueRoles},
        site::OperationIndex,
        terminator::TerminatorKind,
        value::ConstantId,
    },
    module::{FunctionId, ModuleEnv, id::Id},
    std::math::Float,
    wasm::abi::{CallAbi, Parameter as ParameterTransport, ResultKind, WasmFunctionId},
};

use super::{
    body::intrinsic_reads_input_repeatedly, control_flow::conditional_targets,
    is_elided_stack_operation, is_fallible_intrinsic, layout_witness, scalar, wasm_intrinsic,
};

const MAX_EXPRESSION_DEPTH: usize = 128;

define_id_type!(
    /// An operation or terminator slot in the function-wide dense operation tables.
    FlatOperationId
);
define_id_type!(
    /// A scalar producer considered for deferred emission.
    CandidateId
);
define_id_type!(
    /// A parameter or register slot in the dense place tables.
    PlaceSlotId
);
define_id_type!(
    /// A parameter, register, or constant slot in the dense value tables.
    DenseValueSlotId
);

/// The location of an operation within a physical MIR function.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) struct Source {
    pub(super) block: BlockId,
    operation: OperationIndex,
}

impl Source {
    pub(super) fn from_index(block: BlockId, operation: usize) -> Self {
        Self {
            block,
            operation: OperationIndex::from_index(operation),
        }
    }

    pub(super) fn operation_id(self) -> OperationIndex {
        self.operation
    }

    /// The operation at this source, including an Invoke at the terminator position.
    fn operation(self, body: &Function) -> Option<&Operation> {
        let block = body.block(self.block);
        let index = self.operation.as_index();
        block.operations().get(index).or_else(|| {
            if index == block.operations().len()
                && let TerminatorKind::Invoke { operation, .. } = &block.terminator().kind
            {
                Some(operation)
            } else {
                None
            }
        })
    }
}

struct OperationLayout {
    bases: Vec<FlatOperationId>,
    operation_count: usize,
}

impl OperationLayout {
    fn of(body: &Function) -> Self {
        let mut bases = Vec::with_capacity(body.blocks().count());
        let mut operation_count = 0;
        for block in body.blocks() {
            bases.push(FlatOperationId::from_index(operation_count));
            // The extra position represents the terminator and can be a group root.
            operation_count += body.block(block).operations().len() + 1;
        }
        Self {
            bases,
            operation_count,
        }
    }

    fn index(&self, source: Source) -> FlatOperationId {
        FlatOperationId::from_index(
            self.bases[source.block.as_index()].as_index() + source.operation.as_index(),
        )
    }
}

/// The tag extraction and predicate are emitted together with their comparison call.
#[derive(Clone, Copy)]
enum ComparisonFusion {
    Test(KnownCallee),
    Switch(KnownCallee),
    Tag,
}

/// Dense facts shared by scalar storage assignment and expression-tree emission.
pub(super) struct Analysis {
    parameter_count: usize,
    register_count: usize,
    operation_bases: Vec<FlatOperationId>,
    addressed: Vec<bool>,
    intrinsics: Vec<Option<KnownCallee>>,
    comparison_fusions: Vec<Option<ComparisonFusion>>,
    value_uses: Vec<Uses>,
    metadata_loads: Vec<bool>,
    definitions: Vec<Option<Source>>,
    integer_constants: FxHashMap<ValueId, i32>,
    scalar_constants: FxHashMap<ValueId, ConstantId>,
    /// The direct result is left on the operand stack by each terminal writer.
    pub(super) stack_return: Option<ParameterId>,
}

impl Analysis {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn of(
        body: &Function,
        roles: &ValueRoles,
        callees: &FxHashMap<FunctionId, (WasmFunctionId, &CallAbi)>,
        program: &ResolvedPhysicalProgram<'_>,
        session: &CompilerSession,
        env: ModuleEnv<'_>,
        returns_direct_place: bool,
        no_op_stack_markers: &FxHashSet<ValueId>,
    ) -> (Self, Plan) {
        let layout = OperationLayout::of(body);
        let mut inputs = Inputs::of(
            body,
            roles,
            callees,
            program,
            session,
            env,
            returns_direct_place,
            &layout,
        );
        let stack_return = returns_direct_place
            .then(|| stack_return(body, &inputs, &layout, callees, program))
            .flatten();
        if let Some(id) = stack_return {
            // Terminal writers emit at their original position, rather than being deferred to a
            // synthetic return-place read. Other expression trees keep their ordinary planning.
            inputs.place_roots[id.as_index()] = false;
        }
        let comparison_fusions = comparison_fusions(body, &layout, &inputs);
        let plan = Plan::of(
            body,
            roles,
            &inputs,
            &comparison_fusions,
            &layout,
            no_op_stack_markers,
            env,
        );
        let metadata_loads = metadata_loads(body, roles, &inputs, &plan, env);
        let analysis = Self {
            parameter_count: body.parameters().len(),
            register_count: roles.register_count(),
            operation_bases: layout.bases,
            addressed: inputs.addressed,
            intrinsics: inputs.intrinsics,
            comparison_fusions,
            value_uses: inputs.value_uses,
            metadata_loads,
            definitions: inputs.definitions,
            integer_constants: inputs.integer_constants,
            scalar_constants: inputs.scalar_constants,
            stack_return,
        };
        (analysis, plan)
    }

    pub(super) fn integer_constant(&self, body: &Function, value: &Value) -> Option<i32> {
        super::body::integer_constant(body, value, &self.definitions, &self.integer_constants)
    }

    /// Resolve primitive float literals using the existing immutable-storage proof.
    pub(super) fn float_constant(&self, body: &Function, value: &Value) -> Option<f64> {
        super::body::literal_constant(body, value, &self.definitions, Some(&self.scalar_constants))?
            .as_primitive_ty::<Float>()
            .map(|value| value.into_inner())
    }

    pub(super) fn scalar_constant(&self, value: &Value) -> Option<ConstantId> {
        let Value::Register(id) = value else {
            return None;
        };
        self.scalar_constants.get(id).copied()
    }

    pub(super) fn skips_metadata_load(&self, operation: &Operation) -> bool {
        operation
            .result_id()
            .is_some_and(|id| self.metadata_loads[id.as_index()])
    }

    pub(super) fn is_addressed(&self, value: &Value) -> bool {
        dense_value_index(value, self.parameter_count, self.register_count)
            .and_then(|id| self.addressed.get(id.as_index()))
            .copied()
            .unwrap_or(false)
    }

    pub(super) fn intrinsic(&self, source: Source) -> Option<KnownCallee> {
        self.intrinsics
            .get(self.operation_index(source).as_index())
            .copied()
            .flatten()
    }

    fn operation_index(&self, source: Source) -> FlatOperationId {
        FlatOperationId::from_index(
            self.operation_bases[source.block.as_index()].as_index()
                + source.operation_id().as_index(),
        )
    }

    /// The only operation or terminator reading register `id`, if exactly one does and emission
    /// cannot skip it.
    pub(super) fn sole_use(&self, id: ValueId) -> Option<Source> {
        self.value_uses
            .get(id.as_index())
            .and_then(|uses| uses.one())
    }

    pub(super) fn comparison_fusion(&self, id: ValueId) -> Option<KnownCallee> {
        self.comparison_fusions
            .get(id.as_index())
            .copied()
            .flatten()
            .and_then(|fusion| match fusion {
                ComparisonFusion::Test(intrinsic) => Some(intrinsic),
                ComparisonFusion::Tag | ComparisonFusion::Switch(_) => None,
            })
    }

    pub(super) fn comparison_switch(&self, block: &BasicBlock) -> Option<KnownCallee> {
        let tag = block.operations().last()?.result_id()?;
        match self.comparison_fusions[tag.as_index()]? {
            ComparisonFusion::Switch(intrinsic) => Some(intrinsic),
            _ => None,
        }
    }
}

/// A scalar output needs no storage when its only uses are final writers at normal returns.
/// Reuse the operand census, then check only return blocks. One output use per return and one
/// valid terminal writer in each block exclude every other read, write or exposed address.
/// The writer must be the literal last operation, even when later operations emit no code.
fn stack_return(
    body: &Function,
    inputs: &Inputs,
    layout: &OperationLayout,
    callees: &FxHashMap<FunctionId, (WasmFunctionId, &CallAbi)>,
    program: &ResolvedPhysicalProgram<'_>,
) -> Option<ParameterId> {
    let id = inputs.return_parameter?;
    let output = Value::Parameter(id);
    if inputs.return_blocks.is_empty()
        || inputs.return_uses != inputs.return_blocks.len()
        || inputs.is_addressed(&output, body.parameters().len(), inputs.value_uses.len())
    {
        return None;
    }
    for &block_id in &inputs.return_blocks {
        let block = body.block(block_id);
        let (operation, _) = block.operations().split_last()?;
        let destination = match &operation.kind {
            OperationKind::Store => Some(1),
            OperationKind::Memcpy | OperationKind::Move | OperationKind::MoveBytes { .. }
                if layout_witness(operation).is_none() =>
            {
                Some(1)
            }
            OperationKind::Call { ty, .. } if ty.result_convention.has_result_place() => {
                let source = Source::from_index(block_id, block.operations().len() - 1);
                let intrinsic = inputs.intrinsic(layout, source);
                let direct = call_abi(operation, intrinsic, callees, program).is_some_and(|abi| {
                    !abi.fallible && matches!(abi.result, ResultKind::Direct(_))
                });
                (intrinsic.is_some_and(|intrinsic| !is_fallible_intrinsic(intrinsic)) || direct)
                    .then_some(operation.operands.len() - 1)
            }
            _ => None,
        };
        if destination.and_then(|index| operation.operands.get(index)) != Some(&output) {
            return None;
        }
    }
    Some(id)
}

/// Scalar producers which may be deferred until their sole consumer is emitted.
#[derive(Default)]
pub(super) struct Plan {
    parameter_count: usize,
    values: Vec<Option<Source>>,
    selected_values: Vec<bool>,
    places: Vec<Option<Source>>,
    writes: Vec<bool>,
}

impl Plan {
    fn of(
        body: &Function,
        roles: &ValueRoles,
        inputs: &Inputs,
        comparison_fusions: &[Option<ComparisonFusion>],
        layout: &OperationLayout,
        no_op_stack_markers: &FxHashSet<ValueId>,
        env: ModuleEnv<'_>,
    ) -> Self {
        let parameter_count = body.parameters().len();
        let value_count = roles.register_count();
        let place_count = parameter_count + value_count;
        let mut candidates = Vec::new();
        let mut definitions = vec![None; layout.operation_count];

        for (index, definition) in inputs.value_definitions.iter().enumerate() {
            let Some(source) = definition else { continue };
            let id = ValueId::from_index(index);
            let value = Value::Register(id);
            let Some(consumer) = inputs.value_uses[index].one() else {
                continue;
            };
            if consumer.block != source.block
                || consumer.operation_id().as_index() <= source.operation_id().as_index()
                || !stackifiable_consumer(body, consumer)
            {
                continue;
            }
            let role = roles.get(&value, body.constants());
            // These producers yield an address, rather than allocating storage whose identity
            // needs a local. Defer only to consumers that emit that address exactly once.
            let address_result = role.as_ref().is_some_and(|role| {
                matches!(&**role, ValueRole::Materialized(MirType::Pointer(_)))
                    || matches!(&**role, ValueRole::Place(_))
                        && matches!(
                            body.block(source.block).operations()[source.operation_id().as_index()]
                                .kind,
                            OperationKind::AddressOffset { .. }
                                | OperationKind::AddressOffsetPlace { .. }
                        )
            });
            let address_consumer = if address_result {
                consumer.operation(body).and_then(|operation| {
                    stackifiable_address_consumer(operation, body, roles, &inputs.definitions, env)
                })
            } else {
                None
            };
            if address_consumer == Some(false) {
                continue;
            }
            // Other consumers retain the ordinary scalar path for materialized pointers,
            // including the address-exposure check. A place is not a scalar value.
            let address_result = address_consumer == Some(true);
            if !address_result && inputs.is_addressed(&value, parameter_count, value_count)
                || comparison_fusions[id.as_index()].is_some()
            {
                continue;
            }
            let scalar_result = address_result
                || role.is_some_and(|role| {
                    matches!(&*role, ValueRole::VariantTag)
                        || matches!(&*role, ValueRole::Materialized(ty) if scalar(ty, &env).is_ok())
                });
            if !scalar_result {
                continue;
            }
            let candidate = CandidateId::from_index(candidates.len());
            candidates.push(Candidate {
                target: Target::Value(id),
                source: *source,
                consumer,
            });
            definitions[layout.index(*source).as_index()] = Some(candidate);
        }

        for index in 0..place_count {
            if !inputs.place_roots[index] {
                continue;
            }
            let value = if index < parameter_count {
                Value::Parameter(ParameterId::from_index(index))
            } else {
                Value::Register(ValueId::from_index(index - parameter_count))
            };
            if inputs.is_addressed(&value, parameter_count, value_count)
                || matches!(&value, Value::Register(id) if inputs.scalar_constants.contains_key(id))
                || !roles
                    .get(&value, body.constants())
                    .and_then(|role| role.place_pointee_type())
                    .is_some_and(|ty| scalar(&ty, &env).is_ok())
            {
                continue;
            }
            let Some((first, second)) = inputs.place_accesses[index].pair() else {
                continue;
            };
            let (write, read) =
                if first.kind == AccessKind::Write && second.kind == AccessKind::Read {
                    (first, second)
                } else if second.kind == AccessKind::Write && first.kind == AccessKind::Read {
                    (second, first)
                } else {
                    continue;
                };
            if write.source.block != read.source.block
                || write.source.operation_id().as_index() >= read.source.operation_id().as_index()
                || !stackifiable_consumer(body, read.source)
            {
                continue;
            }
            let Some(writer) = body
                .block(write.source.block)
                .operations()
                .get(write.source.operation_id().as_index())
            else {
                continue;
            };
            let supported =
                match writer.kind {
                    OperationKind::Store => true,
                    OperationKind::Call { .. } => inputs
                        .intrinsic(layout, write.source)
                        .is_some_and(|callee| {
                            !is_fallible_intrinsic(callee)
                                && !matches!(callee, KnownCallee::IntCmp | KnownCallee::FloatCmp)
                        }),
                    _ => false,
                };
            if !supported {
                continue;
            }
            let candidate = CandidateId::from_index(candidates.len());
            candidates.push(Candidate {
                target: Target::Place(PlaceSlotId::from_index(index)),
                source: write.source,
                consumer: read.source,
            });
            let source = layout.index(write.source).as_index();
            debug_assert!(definitions[source].is_none());
            definitions[source] = Some(candidate);
        }

        if candidates.is_empty() {
            return Self::default();
        }

        // A producer whose sole consumer is a producer of the same kind joins that consumer's
        // group. Keeping value and place groups separate permits an inner group to remain
        // stackified when an enclosing group is rejected. `ultimate_roots` still relates nested
        // groups, so their combined effect-free window does not cause an enclosing group to be
        // rejected merely because it contains an independently accepted group.
        //
        // Processing definitions backwards makes both roots available without a walk.
        let mut roots = vec![None; layout.operation_count];
        let mut ultimate_roots = vec![None; layout.operation_count];
        let mut depths = vec![0_usize; layout.operation_count];
        let mut group_first = vec![None::<FlatOperationId>; layout.operation_count];
        let mut group_depth = vec![0_usize; layout.operation_count];
        let mut group_ultimate_root = vec![None::<FlatOperationId>; layout.operation_count];
        for block_id in body.blocks() {
            for operation in (0..body.block(block_id).operations().len()).rev() {
                let source = Source::from_index(block_id, operation);
                let source_id = layout.index(source);
                let source_index = source_id.as_index();
                let Some(candidate_id) = definitions[source_index] else {
                    continue;
                };
                let candidate = candidates[candidate_id.as_index()];
                let consumer = layout.index(candidate.consumer);
                let dependency = definitions[consumer.as_index()];
                depths[source_index] = dependency
                    .map(|next| {
                        depths[layout.index(candidates[next.as_index()].source).as_index()] + 1
                    })
                    .unwrap_or(1);
                let ultimate_root = dependency
                    .and_then(|next| {
                        ultimate_roots[layout.index(candidates[next.as_index()].source).as_index()]
                    })
                    .unwrap_or(consumer);
                ultimate_roots[source_index] = Some(ultimate_root);
                let root = definitions[consumer.as_index()]
                    .filter(|&next| {
                        matches!(
                            (candidate.target, candidates[next.as_index()].target),
                            (Target::Value(_), Target::Value(_))
                                | (Target::Place(_), Target::Place(_))
                        )
                    })
                    .and_then(|next| {
                        roots[layout.index(candidates[next.as_index()].source).as_index()]
                    })
                    .unwrap_or(consumer);
                roots[source_index] = Some(root);
                let root_index = root.as_index();
                group_first[root_index] = Some(
                    group_first[root_index]
                        .filter(|first| first.as_index() < source_index)
                        .unwrap_or(source_id),
                );
                group_depth[root_index] = group_depth[root_index].max(depths[source_index]);
                if let Some(group_root) = group_ultimate_root[root_index] {
                    debug_assert_eq!(group_root, ultimate_root);
                } else {
                    group_ultimate_root[root_index] = Some(ultimate_root);
                }
            }
        }

        // What each tree's producers read, by position. Deferral moves a producer down to its
        // tree's root, so it must not cross a write to one of these.
        let mut tree_reads: FxHashMap<FlatOperationId, Vec<(usize, PlaceSlotId)>> =
            FxHashMap::default();
        for candidate in &candidates {
            let source = layout.index(candidate.source).as_index();
            let Some(ultimate_root) = ultimate_roots[source] else {
                continue;
            };
            let producer = &body.block(candidate.source.block).operations()
                [candidate.source.operation_id().as_index()];
            let reads = tree_reads.entry(ultimate_root).or_default();
            for (index, operand) in producer.operands.iter().enumerate() {
                if is_metadata_operand(producer, index) {
                    continue;
                }
                if let Some(slot) = place_index(operand, parameter_count) {
                    reads.push((source, slot));
                }
            }
        }

        let mut accepted = vec![false; layout.operation_count];
        for block_id in body.blocks() {
            let block = body.block(block_id);
            let base = layout.bases[block_id.as_index()];
            for root_offset in 0..=block.operations().len() {
                let root_source = Source::from_index(block_id, root_offset);
                let root = layout.index(root_source);
                let root_index = root.as_index();
                let Some(first) = group_first[root_index] else {
                    continue;
                };
                if group_depth[root_index] > MAX_EXPRESSION_DEPTH {
                    continue;
                }
                if matches!(
                    inputs.intrinsic(layout, root_source),
                    Some(KnownCallee::IntCmp | KnownCallee::FloatCmp)
                ) && !fused_comparison_call(
                    block,
                    root_source.operation_id(),
                    comparison_fusions,
                ) {
                    // Materializing an ordering tag reads both inputs twice. Keep its arguments
                    // in locals; adjacent predicate fusion has its own single-read path.
                    continue;
                }
                let ultimate_root =
                    group_ultimate_root[root_index].expect("non-empty expression group");
                // Every other operation between the tree's first producer and its root is emitted
                // before the tree. That is invisible unless it writes what an earlier producer
                // reads, or it has effects of its own.
                let reads = tree_reads
                    .get(&ultimate_root)
                    .map_or(&[][..], Vec::as_slice);
                let unaffected = (first.as_index()..root_index).all(|operation| {
                    let offset = operation - base.as_index();
                    let other = &block.operations()[offset];
                    ultimate_roots[operation] == Some(ultimate_root)
                        || is_neutral(other, no_op_stack_markers)
                        || local_writes(
                            other,
                            Source::from_index(block_id, offset),
                            inputs,
                            layout,
                            parameter_count,
                            value_count,
                        )
                        .is_some_and(|writes| {
                            !reads.iter().any(|&(producer, slot)| {
                                producer < operation && writes.contains(&slot)
                            })
                        })
                });
                accepted[root_index] = unaffected;
            }
        }

        let mut values = vec![None; value_count];
        let mut selected_values = vec![false; value_count];
        let mut places = vec![None; place_count];
        let mut writes = vec![false; layout.operation_count];
        for candidate in candidates {
            let source = layout.index(candidate.source);
            if !roots[source.as_index()].is_some_and(|root| accepted[root.as_index()]) {
                continue;
            }
            match candidate.target {
                Target::Value(id) => {
                    values[id.as_index()] = Some(candidate.source);
                    selected_values[id.as_index()] = true;
                }
                Target::Place(id) => {
                    places[id.as_index()] = Some(candidate.source);
                    writes[source.as_index()] = true;
                }
            }
        }
        Self {
            parameter_count,
            values,
            selected_values,
            places,
            writes,
        }
    }

    pub(super) fn has_value(&self, id: ValueId) -> bool {
        self.selected_values
            .get(id.as_index())
            .copied()
            .unwrap_or(false)
    }

    pub(super) fn has_pending_value(&self, id: ValueId) -> bool {
        self.values.get(id.as_index()).is_some_and(Option::is_some)
    }

    pub(super) fn pending_value(&self, id: ValueId) -> Option<Source> {
        self.values.get(id.as_index()).copied().flatten()
    }

    pub(super) fn take_value(&mut self, id: ValueId) -> Option<Source> {
        self.values.get_mut(id.as_index())?.take()
    }

    pub(super) fn has_place(&self, value: &Value) -> bool {
        place_index(value, self.parameter_count)
            .and_then(|id| self.places.get(id.as_index()))
            .is_some_and(Option::is_some)
    }

    pub(super) fn take_place(&mut self, value: &Value) -> Option<Source> {
        let id = place_index(value, self.parameter_count)?;
        self.places.get_mut(id.as_index())?.take()
    }

    pub(super) fn skips(&self, source: Source, analysis: &Analysis) -> bool {
        self.writes
            .get(analysis.operation_index(source).as_index())
            .copied()
            .unwrap_or(false)
    }

    /// Whether every expression of the blocks that were `emitted` has been consumed.
    pub(super) fn is_fully_emitted(&self, emitted: impl Fn(BlockId) -> bool) -> bool {
        self.values
            .iter()
            .chain(&self.places)
            .flatten()
            .all(|source| !emitted(source.block))
    }
}

fn place_index(value: &Value, parameter_count: usize) -> Option<PlaceSlotId> {
    match value {
        Value::Parameter(id) => Some(PlaceSlotId::from_index(id.as_index())),
        Value::Register(id) => Some(PlaceSlotId::from_index(parameter_count + id.as_index())),
        _ => None,
    }
}

fn dense_value_index(
    value: &Value,
    parameter_count: usize,
    register_count: usize,
) -> Option<DenseValueSlotId> {
    match value {
        Value::Parameter(id) => Some(DenseValueSlotId::from_index(id.as_index())),
        Value::Register(id) => Some(DenseValueSlotId::from_index(
            parameter_count + id.as_index(),
        )),
        Value::Constant(id) => Some(DenseValueSlotId::from_index(
            parameter_count + register_count + id.as_index(),
        )),
        _ => None,
    }
}

#[derive(Clone, Copy, Default)]
enum Uses {
    #[default]
    None,
    /// Uses exist only in operands that Wasm never reads.
    Metadata,
    One(Source),
    Two,
    Multiple,
    /// Emission may skip one of the uses, so the value cannot be deferred to its consumer.
    Elidable,
}

impl Uses {
    fn add(&mut self, source: Source) {
        *self = match *self {
            Self::None | Self::Metadata => Self::One(source),
            Self::One(_) => Self::Two,
            Self::Two | Self::Multiple => Self::Multiple,
            Self::Elidable => Self::Elidable,
        };
    }

    fn one(self) -> Option<Source> {
        match self {
            Self::One(source) => Some(source),
            Self::None | Self::Metadata | Self::Two | Self::Multiple | Self::Elidable => None,
        }
    }

    fn is_two(self) -> bool {
        matches!(self, Self::Two)
    }
}

#[derive(Clone, Copy)]
enum Target {
    Value(ValueId),
    Place(PlaceSlotId),
}

#[derive(Clone, Copy)]
struct Candidate {
    target: Target,
    source: Source,
    consumer: Source,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum AccessKind {
    Read,
    Write,
    Unsupported,
}

#[derive(Clone, Copy)]
struct Access {
    source: Source,
    kind: AccessKind,
}

#[derive(Clone, Copy, Default)]
struct Accesses {
    first: Option<Access>,
    second: Option<Access>,
    multiple: bool,
    write: Option<Access>,
    multiple_writes: bool,
    unsupported: bool,
}

impl Accesses {
    fn add(&mut self, access: Access) {
        match access.kind {
            AccessKind::Write if self.write.is_some() => self.multiple_writes = true,
            AccessKind::Write => self.write = Some(access),
            AccessKind::Unsupported => self.unsupported = true,
            AccessKind::Read => (),
        }
        if self.first.is_none() {
            self.first = Some(access);
        } else if self.second.is_none() {
            self.second = Some(access);
        } else {
            self.multiple = true;
        }
    }

    fn pair(self) -> Option<(Access, Access)> {
        (!self.multiple).then_some((self.first?, self.second?))
    }
}

struct Inputs {
    return_parameter: Option<ParameterId>,
    /// Actual MIR occurrences, excluding synthetic reads and intrinsic rereads.
    return_uses: usize,
    return_blocks: SmallVec<[BlockId; 2]>,
    value_uses: Vec<Uses>,
    value_definitions: Vec<Option<Source>>,
    definitions: Vec<Option<Source>>,
    place_roots: Vec<bool>,
    place_accesses: Vec<Accesses>,
    addressed: Vec<bool>,
    intrinsics: Vec<Option<KnownCallee>>,
    integer_constants: FxHashMap<ValueId, i32>,
    scalar_constants: FxHashMap<ValueId, ConstantId>,
}

impl Inputs {
    fn is_addressed(&self, value: &Value, parameter_count: usize, register_count: usize) -> bool {
        dense_value_index(value, parameter_count, register_count)
            .is_some_and(|id| self.addressed[id.as_index()])
    }

    fn intrinsic(&self, layout: &OperationLayout, source: Source) -> Option<KnownCallee> {
        self.intrinsics[layout.index(source).as_index()]
    }

    #[allow(clippy::too_many_arguments)]
    fn of(
        body: &Function,
        roles: &ValueRoles,
        callees: &FxHashMap<FunctionId, (WasmFunctionId, &CallAbi)>,
        program: &ResolvedPhysicalProgram<'_>,
        session: &CompilerSession,
        env: ModuleEnv<'_>,
        returns_direct_place: bool,
        layout: &OperationLayout,
    ) -> Self {
        let value_count = roles.register_count();
        let parameter_count = body.parameters().len();
        let place_count = parameter_count + value_count;
        let mut value_definitions = vec![None; value_count];
        let mut definitions = vec![None; value_count];
        let mut place_roots = vec![false; place_count];
        let mut scan = OperandScan::new(body, roles, parameter_count, value_count, env);
        if returns_direct_place {
            scan.return_parameter = body
                .parameters()
                .iter()
                .position(|parameter| parameter.kind == ParameterKind::Return)
                .map(ParameterId::from_index);
            if let Some(id) = scan.return_parameter {
                place_roots[id.as_index()] = true;
            }
        }
        let mut return_blocks = SmallVec::new();
        let mut intrinsics = vec![None; layout.operation_count];
        let mut intrinsic_calls = Vec::new();
        for block_id in body.blocks() {
            let block = body.block(block_id);
            for (operation, op) in block.operations().iter().enumerate() {
                let source = Source::from_index(block_id, operation);
                if let Some(id) = op.result_id() {
                    definitions[id.as_index()] = Some(source);
                    if matches!(
                        op.kind,
                        OperationKind::Alloca { .. } | OperationKind::AllocaPlace { .. }
                    ) && op.operands.is_empty()
                    {
                        place_roots[parameter_count + id.as_index()] = true;
                    } else if matches!(
                        op.kind,
                        OperationKind::Load
                            | OperationKind::CompareEqual
                            | OperationKind::ExtractTag
                            | OperationKind::ExtractPayloadIndirection
                            | OperationKind::AddressOffset { .. }
                            | OperationKind::AddressOffsetPlace { .. }
                    ) {
                        value_definitions[id.as_index()] = Some(source);
                    }
                }
                let intrinsic = wasm_intrinsic(session, op);
                intrinsics[layout.index(source).as_index()] = intrinsic;
                if let Some(known) = intrinsic {
                    intrinsic_calls.push((source, op, known));
                }
                scan.operands(
                    op,
                    source,
                    intrinsic,
                    call_abi(op, intrinsic, callees, program),
                );
            }
            let source = Source::from_index(block_id, block.operations().len());
            match &block.terminator().kind {
                TerminatorKind::Invoke { operation, .. } => {
                    let intrinsic = wasm_intrinsic(session, operation);
                    intrinsics[layout.index(source).as_index()] = intrinsic;
                    if let Some(known) = intrinsic {
                        intrinsic_calls.push((source, operation, known));
                    }
                    scan.operands(
                        operation,
                        source,
                        intrinsic,
                        call_abi(operation, intrinsic, callees, program),
                    );
                }
                TerminatorKind::Return => {
                    if let Some(id) = scan.return_parameter {
                        return_blocks.push(block_id);
                        // This implicit ABI read is not an occurrence in the MIR use count.
                        scan.place_accesses[id.as_index()].add(Access {
                            source,
                            kind: AccessKind::Read,
                        });
                    }
                }
                _ => {
                    for operand in block.terminator().operands() {
                        scan.operand(operand, source, Some(AccessKind::Read));
                        if !matches!(block.terminator().kind, TerminatorKind::CondBr { .. }) {
                            scan.mark_addressed(operand);
                        }
                    }
                }
            }
        }
        // Freeze the MIR occurrence count before accounting for emitted intrinsic rereads.
        let return_uses = scan.return_uses;
        let scalar_constants = scalar_constants(body, &place_roots, &scan);
        let mut integer_constants = FxHashMap::default();
        for (&id, &constant) in &scalar_constants {
            if let Some(value) = super::body::integer_constant(
                body,
                &Value::Constant(constant),
                &definitions,
                &integer_constants,
            ) {
                integer_constants.insert(id, value);
            }
        }
        // Direct literal stores are covered above. Also specialize a single-read integer place
        // initialized by a load of a literal; its store must still consume that producer.
        for (index, &is_root) in place_roots.iter().enumerate().skip(parameter_count) {
            let id = ValueId::from_index(index - parameter_count);
            if !is_root || scan.addressed[index] {
                continue;
            }
            let Some((first, second)) = scan.place_accesses[index].pair() else {
                continue;
            };
            let (write, read) = match (first.kind, second.kind) {
                (AccessKind::Write, AccessKind::Read) => (first, second),
                (AccessKind::Read, AccessKind::Write) => (second, first),
                _ => continue,
            };
            if write.source.block != read.source.block
                || write.source.operation_id().as_index() >= read.source.operation_id().as_index()
            {
                continue;
            }
            let Some(operation) = body
                .block(write.source.block)
                .operations()
                .get(write.source.operation_id().as_index())
            else {
                continue;
            };
            if !matches!(operation.kind, OperationKind::Store) {
                continue;
            }
            if let Some(constant) = super::body::integer_constant(
                body,
                &operation.operands[0],
                &definitions,
                &integer_constants,
            ) {
                integer_constants.insert(id, constant);
            }
        }
        // Add emitted rereads after discovering immutable literal places from the ordinary census.
        for (source, operation, intrinsic) in intrinsic_calls {
            let OperationKind::Call { ty, .. } = &operation.kind else {
                unreachable!()
            };
            let end =
                operation.operands.len() - usize::from(ty.result_convention.has_result_place());
            let inputs = &operation.operands[1..end];
            for (input, operand) in inputs.iter().enumerate() {
                if intrinsic_reads_input_repeatedly(
                    intrinsic,
                    input,
                    inputs,
                    body,
                    &definitions,
                    &integer_constants,
                    &scalar_constants,
                    source.operation_id().as_index() == body.block(source.block).operations().len(),
                ) {
                    scan.operand(operand, source, classify_access(operation, input + 1));
                }
            }
        }
        Self {
            return_parameter: scan.return_parameter,
            return_uses,
            return_blocks,
            value_uses: scan.value_uses,
            value_definitions,
            definitions,
            place_roots,
            place_accesses: scan.place_accesses,
            addressed: scan.addressed,
            intrinsics,
            integer_constants,
            scalar_constants,
        }
    }
}

/// Literal scalar storage can be rematerialized at every read when its single write dominates
/// them all. Reuse the address/write census, then validate reads in one additional operand scan.
/// Same-block reads need only instruction ordering; build block dominance lazily for other reads.
fn scalar_constants(
    body: &Function,
    place_roots: &[bool],
    scan: &OperandScan<'_>,
) -> FxHashMap<ValueId, ConstantId> {
    let mut constants = FxHashMap::default();
    for (index, accesses) in scan
        .place_accesses
        .iter()
        .enumerate()
        .skip(scan.parameter_count)
    {
        if !place_roots[index]
            || scan.addressed[index]
            || accesses.multiple_writes
            || accesses.unsupported
        {
            continue;
        }
        let Some(write) = accesses.write else {
            continue;
        };
        let Some(operation) = body
            .block(write.source.block)
            .operations()
            .get(write.source.operation_id().as_index())
        else {
            continue;
        };
        if !matches!(operation.kind, OperationKind::Store) {
            continue;
        }
        let Value::Constant(constant) = operation.operands[0] else {
            continue;
        };
        // Restrict this to primitive literals; pointer slots and aggregate/tag representations
        // require their own materialization and ownership rules.
        if super::ScalarType::of(body.constant(constant).ty).is_ok() {
            constants.insert(ValueId::from_index(index - scan.parameter_count), constant);
        }
    }
    if constants.is_empty() {
        return constants;
    }
    let dominance = OnceCell::new();
    let mut check_read = |value: &Value, source: Source| {
        let Value::Register(id) = value else { return };
        if !constants.contains_key(id) {
            return;
        }
        let write = scan.place_accesses[scan.parameter_count + id.as_index()]
            .write
            .unwrap()
            .source;
        let dominates = if write.block == source.block {
            write.operation_id().as_index() < source.operation_id().as_index()
        } else {
            dominance
                .get_or_init(|| {
                    let successors = body
                        .blocks()
                        .map(|block| {
                            body.block(block)
                                .terminator()
                                .successors()
                                .map(|target| target.as_index())
                                .collect()
                        })
                        .collect::<Vec<_>>();
                    Dominance::of(&successors, body.entry().as_index())
                })
                .dominates(write.block.as_index(), source.block.as_index())
        };
        if !dominates {
            constants.remove(id);
        }
    };
    for block_id in body.blocks() {
        let block = body.block(block_id);
        let invoked = match &block.terminator().kind {
            TerminatorKind::Invoke { operation, .. } => Some(operation),
            _ => None,
        };
        for (index, operation) in block.operations().iter().chain(invoked).enumerate() {
            let source = Source::from_index(block_id, index);
            for (index, operand) in operation.operands.iter().enumerate() {
                if !is_metadata_operand(operation, index)
                    && classify_access(operation, index) == Some(AccessKind::Read)
                {
                    check_read(operand, source);
                }
            }
        }
        if invoked.is_none() {
            let source = Source::from_index(block_id, block.operations().len());
            for operand in block.terminator().operands() {
                check_read(operand, source);
            }
        }
    }
    constants
}

struct OperandScan<'a> {
    env: ModuleEnv<'a>,
    body: &'a Function,
    roles: &'a ValueRoles,
    parameter_count: usize,
    register_count: usize,
    return_parameter: Option<ParameterId>,
    return_uses: usize,
    value_uses: Vec<Uses>,
    place_accesses: Vec<Accesses>,
    addressed: Vec<bool>,
}

impl<'a> OperandScan<'a> {
    fn new(
        body: &'a Function,
        roles: &'a ValueRoles,
        parameter_count: usize,
        register_count: usize,
        env: ModuleEnv<'a>,
    ) -> Self {
        Self {
            env,
            body,
            roles,
            parameter_count,
            register_count,
            return_parameter: None,
            return_uses: 0,
            value_uses: vec![Uses::None; register_count],
            place_accesses: vec![Accesses::default(); parameter_count + register_count],
            addressed: vec![false; parameter_count + register_count + body.constants().len()],
        }
    }

    fn operands(
        &mut self,
        operation: &Operation,
        source: Source,
        intrinsic: Option<KnownCallee>,
        call_abi: Option<&CallAbi>,
    ) {
        // Clear ends a MIR lifetime but emits no read or write of its backing bytes.
        if matches!(operation.kind, OperationKind::Clear) {
            for operand in &operation.operands {
                self.count_return_use(operand);
            }
            return;
        }
        for (index, operand) in operation.operands.iter().enumerate() {
            if is_metadata_operand(operation, index) {
                self.count_return_use(operand);
                if let Value::Register(id) = operand
                    && matches!(self.value_uses[id.as_index()], Uses::None)
                {
                    self.value_uses[id.as_index()] = Uses::Metadata;
                }
                continue;
            }
            self.operand(operand, source, classify_access(operation, index));
            if is_elidable_operand(operation, index) {
                self.elidable_operand(operand);
            }
            if observes_address(
                operation, index, intrinsic, call_abi, self.roles, self.body, self.env,
            ) {
                self.mark_addressed(operand);
            }
        }
    }

    fn elidable_operand(&mut self, operand: &Value) {
        if let Value::Register(id) = operand {
            self.value_uses[id.as_index()] = Uses::Elidable;
        }
    }

    fn count_return_use(&mut self, operand: &Value) {
        if let Value::Parameter(id) = operand
            && Some(*id) == self.return_parameter
        {
            self.return_uses += 1;
        }
    }

    fn operand(&mut self, operand: &Value, source: Source, kind: Option<AccessKind>) {
        self.count_return_use(operand);
        if let Value::Register(id) = operand {
            self.value_uses[id.as_index()].add(source);
        }
        let Some(kind) = kind else { return };
        let Some(id) = place_index(operand, self.parameter_count) else {
            return;
        };
        self.place_accesses[id.as_index()].add(Access { source, kind });
    }

    fn mark_addressed(&mut self, value: &Value) {
        if let Some(id) = dense_value_index(value, self.parameter_count, self.register_count) {
            self.addressed[id.as_index()] = true;
        }
    }
}

fn call_abi<'a>(
    operation: &Operation,
    intrinsic: Option<KnownCallee>,
    callees: &'a FxHashMap<FunctionId, (WasmFunctionId, &CallAbi)>,
    program: &ResolvedPhysicalProgram<'_>,
) -> Option<&'a CallAbi> {
    if intrinsic.is_some() || !matches!(operation.kind, OperationKind::Call { .. }) {
        return None;
    }
    let Value::Function(target) = operation.operands.first()? else {
        return None;
    };
    callees
        .get(&program.direct_entry(*target))
        .map(|(_, abi)| *abi)
}

/// Whether an operand's address, rather than only its scalar contents, is observed.
///
/// Offset derivation, pointer storage, indirect arguments, and unmodelled uses conservatively
/// observe the address. Since deriving an alias observes its root, expression planning does not
/// require alias analysis.
fn observes_address(
    operation: &Operation,
    index: usize,
    intrinsic: Option<KnownCallee>,
    call_abi: Option<&CallAbi>,
    roles: &ValueRoles,
    body: &Function,
    env: ModuleEnv<'_>,
) -> bool {
    match &operation.kind {
        OperationKind::ExtractTag | OperationKind::ExtractPayloadIndirection => roles
            .get(&operation.operands[index], body.constants())
            .and_then(|role| role.place_pointee_type())
            .is_none_or(|ty| scalar(&ty, &env).is_err()),
        OperationKind::Load
        | OperationKind::Clear
        | OperationKind::Memcpy
        | OperationKind::Move
        | OperationKind::MoveBytes { .. }
        | OperationKind::CompareEqual => false,
        OperationKind::Store if index == 1 => false,
        // Scalar elements are read by value; the destination is the last operand.
        OperationKind::BuildArray { element_ty } if index + 1 < operation.operands.len() => {
            scalar(&MirType::Lowered(*element_ty), &env).is_err()
        }
        OperationKind::Store => roles
            .get(&operation.operands[index], body.constants())
            .is_some_and(|role| role.is_place_operand()),
        OperationKind::AddressOffset { .. } | OperationKind::AddressOffsetPlace { .. }
            if index == 1 =>
        {
            false
        }
        OperationKind::Call { ty, .. } => {
            if intrinsic.is_some() {
                false
            } else if index + 1 == operation.operands.len()
                && ty.result_convention.has_result_place()
            {
                call_abi.is_none_or(CallAbi::output)
            } else {
                !index
                    .checked_sub(1)
                    .and_then(|input| call_abi?.parameters.get(input))
                    .is_some_and(|parameter| matches!(parameter, ParameterTransport::Direct(_)))
            }
        }
        _ => true,
    }
}

/// Reuse the operand census to find scalar loads used only by interpreter metadata.
fn metadata_loads(
    body: &Function,
    roles: &ValueRoles,
    inputs: &Inputs,
    plan: &Plan,
    env: ModuleEnv<'_>,
) -> Vec<bool> {
    inputs
        .definitions
        .iter()
        .enumerate()
        .map(|(index, source)| {
            if !matches!(inputs.value_uses[index], Uses::Metadata) {
                return false;
            }
            let Some(source) = source else { return false };
            let operation =
                &body.block(source.block).operations()[source.operation_id().as_index()];
            if !matches!(operation.kind, OperationKind::Load) {
                return false;
            }
            // Keep the load if its source is deferred: skipping it would discard that producer,
            // including any nested place writes, and leave an unconsumed expression in the plan.
            let address = &operation.operands[0];
            if plan.has_place(address)
                || matches!(address, Value::Register(id) if plan.has_value(*id))
            {
                return false;
            }
            // Evidence and aggregate loads keep their ownership and materialization work.
            let value = Value::Register(ValueId::from_index(index));
            roles.get(&value, body.constants()).is_some_and(
                |role| matches!(&*role, ValueRole::Materialized(ty) if scalar(ty, &env).is_ok()),
            )
        })
        .collect()
}

/// The logical index accompanies an indexed byte address for interpreter provenance only.
fn is_metadata_operand(operation: &Operation, index: usize) -> bool {
    matches!(operation.kind, OperationKind::AddressOffset { .. }) && index == 2
}

/// Whether emission may skip reading an operand.
///
/// Scalar byte moves are emitted as a load and store of their pointee type, leaving their explicit
/// size unread.
fn is_elidable_operand(operation: &Operation, index: usize) -> bool {
    matches!(operation.kind, OperationKind::MoveBytes { .. }) && index == 2
}

fn classify_access(op: &Operation, index: usize) -> Option<AccessKind> {
    if matches!(op.kind, OperationKind::Clear) {
        return None;
    }
    Some(match &op.kind {
        OperationKind::Store if index == 1 => AccessKind::Write,
        OperationKind::Call { ty, .. }
            if index + 1 == op.operands.len() && ty.result_convention.has_result_place() =>
        {
            AccessKind::Write
        }
        OperationKind::Memcpy | OperationKind::Move | OperationKind::MoveBytes { .. }
            if index == 1 =>
        {
            AccessKind::Unsupported
        }
        OperationKind::Clone { .. } if index == 1 => AccessKind::Unsupported,
        _ => AccessKind::Read,
    })
}

/// The storage `operation` writes, if it has no other effect and writes only scalar roots whose
/// address nothing observes, which therefore only operands naming them can access.
fn local_writes(
    operation: &Operation,
    source: Source,
    inputs: &Inputs,
    layout: &OperationLayout,
    parameter_count: usize,
    value_count: usize,
) -> Option<Vec<PlaceSlotId>> {
    // In-block calls promise success, including fallible intrinsics used as plain calls.
    let written = match operation.kind {
        OperationKind::Load | OperationKind::CompareEqual => None,
        OperationKind::Store | OperationKind::Memcpy => Some(1),
        OperationKind::Call { ref ty, .. } if inputs.intrinsic(layout, source).is_some() => ty
            .result_convention
            .has_result_place()
            .then(|| operation.operands.len() - 1),
        _ => return None,
    };
    let Some(written) = written else {
        return Some(Vec::new());
    };
    let place = &operation.operands[written];
    let slot = place_index(place, parameter_count)?;
    (inputs.place_roots[slot.as_index()]
        && !inputs.is_addressed(place, parameter_count, value_count))
    .then(|| vec![slot])
}

fn is_neutral(operation: &Operation, no_op_stack_markers: &FxHashSet<ValueId>) -> bool {
    matches!(
        operation.kind,
        OperationKind::Alloca { .. } | OperationKind::AllocaPlace { .. } | OperationKind::Clear
    ) || is_elided_stack_operation(operation, no_op_stack_markers)
}

fn stackifiable_operation(operation: &Operation) -> bool {
    matches!(
        operation.kind,
        OperationKind::Load
            | OperationKind::Store
            | OperationKind::Memcpy
            | OperationKind::Move
            | OperationKind::MoveBytes { .. }
            | OperationKind::CompareEqual
            | OperationKind::AddressOffset { .. }
            | OperationKind::AddressOffsetPlace { .. }
            | OperationKind::Variant { .. }
            | OperationKind::RuntimeAlloc { .. }
            | OperationKind::Call { .. }
    )
}

/// Whether an address consumer reads each address exactly once before any call.
/// Returns None for other operations, whose materialized pointers follow scalar planning.
///
/// Scalar accesses and fixed copies evaluate each address once. Literal aggregate initialization
/// and aggregate comparison may reread an address. Evidence loads and witnessed moves can call out
/// before reading their operands, so retain their producers at the original position.
fn stackifiable_address_consumer(
    operation: &Operation,
    body: &Function,
    roles: &ValueRoles,
    definitions: &[Option<Source>],
    env: ModuleEnv<'_>,
) -> Option<bool> {
    // Selected methods allocate and retain their evidence before reading the destination,
    // then read it twice. Trace the same DictEntry/Load chain as callable::selections.
    if matches!(
        operation.kind,
        OperationKind::Store
            | OperationKind::Memcpy
            | OperationKind::Move
            | OperationKind::MoveBytes { .. }
    ) {
        let mut source = &operation.operands[0];
        while let Value::Register(id) = source {
            let Some(producer) = definitions[id.as_index()].and_then(|site| site.operation(body))
            else {
                break;
            };
            match producer.kind {
                OperationKind::DictEntry { .. } => return Some(false),
                OperationKind::Load => source = &producer.operands[0],
                _ => break,
            }
        }
    }
    let scalar_place = |value: &Value| {
        roles
            .get(value, body.constants())
            .and_then(|role| role.place_pointee_type())
            .is_some_and(|ty| scalar(&ty, &env).is_ok())
    };
    Some(match operation.kind {
        OperationKind::Load => operation.result_id().is_some_and(|id| {
            roles
                .get(&Value::Register(id), body.constants())
                .is_some_and(|role| matches!(&*role, ValueRole::Materialized(_)))
        }),
        OperationKind::Store => {
            // Literal aggregate initialization may reread its destination; a materialized
            // source uses one copy. Opaque dictionary selections stay outside this rule.
            scalar_place(&operation.operands[1])
                || matches!(
                    operation.operands[0],
                    Value::Register(_) | Value::Parameter(_)
                ) && roles
                    .get(&operation.operands[0], body.constants())
                    .is_some_and(|role| matches!(&*role, ValueRole::Materialized(_)))
        }
        OperationKind::Memcpy | OperationKind::Move => {
            layout_witness(operation).is_none()
                && roles
                    .get(&operation.operands[0], body.constants())
                    .is_some_and(|role| role.place_pointee_type().is_some())
        }
        OperationKind::MoveBytes { .. } => {
            layout_witness(operation).is_none() && scalar_place(&operation.operands[1])
        }
        OperationKind::CompareEqual => scalar_place(&operation.operands[0]),
        OperationKind::ExtractTag
        | OperationKind::ExtractPayloadIndirection
        | OperationKind::RuntimeDealloc
        | OperationKind::AddressOffset { .. }
        | OperationKind::AddressOffsetPlace { .. } => true,
        _ => return None,
    })
}

/// Whether emission consumes eligible scalar operands exactly once before performing effects.
///
/// This is deliberately an allow-list: adding a MIR operation cannot silently make deferred
/// producers sound without also documenting its emission contract here.
fn stackifiable_consumer(body: &Function, source: Source) -> bool {
    if let Some(operation) = source.operation(body) {
        return stackifiable_operation(operation)
            || matches!(
                operation.kind,
                OperationKind::RuntimeDealloc
                    | OperationKind::ExtractTag
                    | OperationKind::ExtractPayloadIndirection
            );
    }
    matches!(
        body.block(source.block).terminator().kind,
        TerminatorKind::CondBr { .. } | TerminatorKind::Return
    )
}

fn fused_comparison_call(
    block: &BasicBlock,
    operation: OperationIndex,
    comparison_fusions: &[Option<ComparisonFusion>],
) -> bool {
    let operations = block.operations();
    let offset = operation.as_index();
    operations
        .get(offset + 2)
        .and_then(Operation::result_id)
        .is_some_and(|id| {
            matches!(
                comparison_fusions[id.as_index()],
                Some(ComparisonFusion::Test(_))
            )
        })
        || (offset + 2 == operations.len()
            && operations
                .get(offset + 1)
                .and_then(Operation::result_id)
                .is_some_and(|id| {
                    matches!(
                        comparison_fusions[id.as_index()],
                        Some(ComparisonFusion::Switch(_))
                    )
                }))
}

/// Finds comparison calls whose fresh, unaliased output is tested immediately.
///
/// Adjacency keeps the comparison inputs live until the test is emitted. Requiring a fresh
/// `Alloca` output and exactly the call plus test uses permits omission of the materialized
/// ordering tag without leaving observable stale memory behind.
fn comparison_fusions(
    body: &Function,
    layout: &OperationLayout,
    inputs: &Inputs,
) -> Vec<Option<ComparisonFusion>> {
    let mut fused = vec![None; inputs.value_uses.len()];
    for block_id in body.blocks() {
        let operations = body.block(block_id).operations();
        for (index, pair) in operations.windows(2).enumerate() {
            let [call, extract] = pair else {
                unreachable!()
            };
            let Some(intrinsic @ (KnownCallee::IntCmp | KnownCallee::FloatCmp)) =
                inputs.intrinsics[layout.index(Source::from_index(block_id, index)).as_index()]
            else {
                continue;
            };
            let OperationKind::Call { ty, .. } = &call.kind else {
                continue;
            };
            if !ty.result_convention.has_result_place()
                || !matches!(extract.kind, OperationKind::ExtractTag)
                || call.operands.len() != 4
            {
                continue;
            }
            let output = &call.operands[3];
            let Value::Register(output_id) = output else {
                continue;
            };
            let Some(tag_id) = extract.result_id() else {
                continue;
            };
            let fresh_output = inputs.definitions[output_id.as_index()].is_some_and(|source| {
                matches!(
                    body.block(source.block).operations()[source.operation_id().as_index()].kind,
                    OperationKind::Alloca { .. }
                )
            });
            if extract.operands[0] != *output
                || inputs.value_uses[tag_id.as_index()].one().is_none()
                || !inputs.value_uses[output_id.as_index()].is_two()
                || !fresh_output
            {
                continue;
            }
            if let Some(test) = operations.get(index + 2) {
                if !matches!(test.kind, OperationKind::CompareEqual)
                    || test.operands.len() != 2
                    || test.operands[0] != Value::Register(tag_id)
                {
                    continue;
                }
                let Value::Pattern(pattern) = &test.operands[1] else {
                    continue;
                };
                if !pattern
                    .as_variant_tag()
                    .is_some_and(|tag| matches!(tag.as_str(), "Less" | "Equal" | "Greater"))
                {
                    continue;
                }
                if let Some(result) = test.result_id() {
                    fused[result.as_index()] = Some(ComparisonFusion::Test(intrinsic));
                    fused[tag_id.as_index()] = Some(ComparisonFusion::Tag);
                }
            } else {
                let terminator = &body.block(block_id).terminator().kind;
                let TerminatorKind::SwitchVariant {
                    tag,
                    cases,
                    default,
                } = terminator
                else {
                    continue;
                };
                let targets = ["Less", "Equal", "Greater"].map(|tag| {
                    cases
                        .iter()
                        .find(|(case, _)| case.as_str() == tag)
                        .map_or(*default, |(_, target)| *target)
                });
                if *tag == Value::Register(tag_id)
                    && targets.iter().any(|target| *target != targets[0])
                    && conditional_targets(terminator).is_some_and(|(yes, no)| yes != no)
                {
                    fused[tag_id.as_index()] = Some(ComparisonFusion::Switch(intrinsic));
                }
            }
        }
    }
    fused
}

#[cfg(test)]
mod tests {
    use wasm_bindgen_test::wasm_bindgen_test;

    use super::super::script_abi;
    use super::*;
    use crate::{
        Location,
        containers::b,
        hir::{function::ArgConvention, value::LiteralValue},
        mir::{builder::FunctionBuilder, terminator::Terminator},
        module::Path,
        std::{buffer::buffer_type, logic::bool_type, math::int_type},
        types::{
            r#trait::TraitDictionaryEntryIndex,
            r#type::{CallImplType, CallResultConvention, Type},
        },
        ustr,
    };

    #[wasm_bindgen_test]
    fn wasm_codegen_stack_returns_require_terminal_unexposed_writes() {
        let mut session = CompilerSession::new();
        let module = session
            .compile(
                "fn seed() {}",
                "return_plan",
                Path::single_str("return_plan"),
            )
            .unwrap()
            .module_id;
        let program = session.prepare_physical_program(module).unwrap();
        let env = session.module_env();
        let span = Location::new_synthesized();
        for case in [
            "stores",
            "copies",
            "read",
            "address",
            "nonterminal",
            "join",
            "self copy",
            "clear",
        ] {
            let mut builder = FunctionBuilder::new(case.into(), CallResultConvention::Value);
            let condition = Value::Parameter(
                builder.add_parameter(bool_type(), ParameterKind::Parameter(ArgConvention::Let)),
            );
            let id = builder.add_parameter(int_type(), ParameterKind::Return);
            let output = Value::Parameter(id);
            let entry = builder.add_block();
            let left = builder.add_block();
            let right = builder.add_block();
            let join = (case == "join").then(|| builder.add_block());
            let one = Value::Constant(builder.add_constant(
                int_type(),
                LiteralValue::new_native(1_isize),
                &env,
            ));
            let condition = builder
                .append_operation(entry, Operation::load(span, condition))
                .unwrap();
            builder.set_terminator(entry, Terminator::cond_br(span, condition, left, right));
            for block in [left, right] {
                if case == "copies" {
                    let cell = builder
                        .append_operation(block, Operation::alloca(span, int_type()))
                        .unwrap();
                    builder
                        .append_operation(block, Operation::store(span, one.clone(), cell.clone()));
                    builder.append_operation(block, Operation::memcpy(span, cell, output.clone()));
                } else {
                    if case == "address" {
                        builder.append_operation(
                            block,
                            Operation::address_offset(
                                span,
                                output.clone(),
                                one.clone(),
                                int_type(),
                                None,
                            ),
                        );
                    }
                    if case == "clear" {
                        builder.append_operation(block, Operation::clear(span, output.clone()));
                    }
                    builder.append_operation(
                        block,
                        Operation::store(span, one.clone(), output.clone()),
                    );
                    match case {
                        "read" => {
                            builder.append_operation(block, Operation::load(span, output.clone()));
                        }
                        "nonterminal" => {
                            builder.append_operation(block, Operation::alloca(span, int_type()));
                        }
                        "self copy" => {
                            builder.append_operation(
                                block,
                                Operation::memcpy(span, output.clone(), output.clone()),
                            );
                        }
                        _ => (),
                    }
                }
                builder.set_terminator(
                    block,
                    join.map_or_else(
                        || Terminator::ret(span),
                        |join| Terminator::goto(span, join),
                    ),
                );
            }
            if let Some(join) = join {
                builder.set_terminator(join, Terminator::ret(span));
            }
            let body = builder.finish_physical(env);
            let roles = ValueRoles::derive(&body);
            for direct in [false, true] {
                let (analysis, plan) = Analysis::of(
                    &body,
                    &roles,
                    &FxHashMap::default(),
                    &program,
                    &session,
                    env,
                    direct,
                    &FxHashSet::default(),
                );
                assert_eq!(
                    analysis.stack_return,
                    (direct && matches!(case, "stores" | "copies")).then_some(id),
                    "{case}, direct={direct}"
                );
                if analysis.stack_return.is_some() {
                    assert!(
                        !plan.has_place(&output),
                        "terminal writers must not be deferred"
                    );
                }
            }
        }
    }

    #[wasm_bindgen_test]
    fn wasm_codegen_literal_rematerialization_requires_dominating_write() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        for case in ["both branches", "branch write", "read before write", "loop"] {
            let mut builder = FunctionBuilder::new(case.into(), CallResultConvention::NoValue);
            let entry = builder.add_block();
            let left = builder.add_block();
            let right = builder.add_block();
            let join = builder.add_block();
            let literal = builder.add_constant(int_type(), LiteralValue::new_native(3_isize), &env);
            let condition = Value::Constant(builder.add_constant(
                bool_type(),
                LiteralValue::new_native(true),
                &env,
            ));
            let cell = builder
                .append_operation(entry, Operation::alloca(span, int_type()))
                .unwrap();
            if case == "read before write" {
                builder.append_operation(entry, Operation::load(span, cell.clone()));
            }
            let write_block = if case == "branch write" || case == "loop" {
                left
            } else {
                entry
            };
            builder.append_operation(
                write_block,
                Operation::store(span, Value::Constant(literal), cell.clone()),
            );
            if case == "loop" {
                builder.set_terminator(entry, Terminator::goto(span, left));
            } else {
                builder.set_terminator(
                    entry,
                    Terminator::cond_br(span, condition.clone(), left, right),
                );
            }
            builder.append_operation(left, Operation::load(span, cell.clone()));
            if matches!(case, "both branches" | "read before write") {
                builder.append_operation(right, Operation::load(span, cell.clone()));
            }
            builder.append_operation(join, Operation::load(span, cell.clone()));
            if case == "loop" {
                builder.set_terminator(left, Terminator::cond_br(span, condition, left, join));
            } else {
                builder.set_terminator(left, Terminator::goto(span, join));
            }
            builder.set_terminator(right, Terminator::goto(span, join));
            builder.set_terminator(join, Terminator::ret(span));
            // Rejected cases deliberately model uninitialized reads. The physical verifier
            // checks roles and SSA, leaving storage initialization to the executor; do not run them.
            let body = builder.finish_physical(env);
            let roles = ValueRoles::derive(&body);
            let mut scan = OperandScan::new(&body, &roles, 0, roles.register_count(), env);
            for block in body.blocks() {
                for (index, operation) in body.block(block).operations().iter().enumerate() {
                    scan.operands(operation, Source::from_index(block, index), None, None);
                }
            }
            let Value::Register(id) = cell else {
                unreachable!()
            };
            let mut roots = vec![false; roles.register_count()];
            roots[id.as_index()] = true;
            let constants = scalar_constants(&body, &roots, &scan);
            assert_eq!(
                constants.get(&id).copied(),
                matches!(case, "both branches" | "loop").then_some(literal),
                "{case}"
            );
        }
    }

    #[wasm_bindgen_test]
    fn wasm_codegen_address_deferral_requires_single_address_consumption() {
        let mut session = CompilerSession::new();
        let module = session
            .compile(
                "#[inline(never)] fn consume(x: int) {}
                 #[inline(never)] fn checked(x: int) { let a = [0]; a[x]; }",
                "address_guard",
                Path::single_str("address_guard"),
            )
            .unwrap()
            .module_id;
        let program = session.prepare_physical_program(module).unwrap();
        let env = session.module_env();
        let span = Location::new_synthesized();
        let targets = ["consume", "checked"].map(|name| {
            let local = session
                .expect_fresh_module(module)
                .get_local_function_id(ustr(name))
                .unwrap();
            let callee = FunctionId::new(module, local);
            let definition = &session
                .expect_fresh_module(module)
                .get_function_by_id(local)
                .unwrap()
                .definition;
            let body = program.function(callee).unwrap();
            (
                callee,
                CallImplType::new(definition.ty_scheme.ty.clone(), body.result_convention()),
                script_abi(program.function(program.direct_entry(callee)).unwrap(), env).unwrap(),
            )
        });
        let callees = targets
            .iter()
            .map(|(callee, _, abi)| {
                (
                    program.direct_entry(*callee),
                    (WasmFunctionId::from_index(0), abi),
                )
            })
            .collect();

        for aggregate in [false, true] {
            let ty = if aggregate {
                Type::tuple(vec![int_type(), int_type()])
            } else {
                int_type()
            };
            let literal = if aggregate {
                LiteralValue::new_tuple([
                    LiteralValue::new_native(5_isize),
                    LiteralValue::new_native(7_isize),
                ])
            } else {
                LiteralValue::new_native(5_isize)
            };
            for pointer_slot in [false, true] {
                for case in [
                    "load",
                    "store",
                    "copy source",
                    "copy destination",
                    "move source",
                    "move destination",
                    "bytes source",
                    "bytes destination",
                    "compare",
                    "self copy",
                    "direct call",
                    "invoke",
                ] {
                    if aggregate && matches!(case, "direct call" | "invoke") {
                        continue;
                    }
                    let mut builder =
                        FunctionBuilder::new(case.into(), CallResultConvention::NoValue);
                    let base = Value::Parameter(
                        builder
                            .add_parameter(ty, ParameterKind::Parameter(ArgConvention::MutableRef)),
                    );
                    let other = Value::Parameter(
                        builder
                            .add_parameter(ty, ParameterKind::Parameter(ArgConvention::MutableRef)),
                    );
                    let block = builder.add_block();
                    let zero = Value::Constant(builder.add_constant(
                        int_type(),
                        LiteralValue::new_native(0_isize),
                        &env,
                    ));
                    let value = Value::Constant(builder.add_constant(ty, literal.clone(), &env));
                    let size = Value::Constant(builder.add_constant(
                        int_type(),
                        LiteralValue::new_native(if aggregate { 8_isize } else { 4_isize }),
                        &env,
                    ));
                    let address = if pointer_slot {
                        let slot = builder
                            .append_operation(block, Operation::alloca_place(span, ty))
                            .unwrap();
                        builder.append_operation(block, Operation::store(span, base, slot.clone()));
                        builder
                            .append_operation(block, Operation::load(span, slot))
                            .unwrap()
                    } else {
                        builder
                            .append_operation(
                                block,
                                Operation::address_offset(span, base, zero.clone(), ty, None),
                            )
                            .unwrap()
                    };
                    let operation = match case {
                        "load" => Operation::load(span, address.clone()),
                        "store" => Operation::store(span, value, address.clone()),
                        "copy source" => Operation::memcpy(span, address.clone(), other),
                        "copy destination" => Operation::memcpy(span, other, address.clone()),
                        "move source" => Operation::move_value(span, address.clone(), other),
                        "move destination" => Operation::move_value(span, other, address.clone()),
                        "bytes source" => {
                            Operation::move_bytes(span, ty, address.clone(), other, size)
                        }
                        "bytes destination" => {
                            Operation::move_bytes(span, ty, other, address.clone(), size)
                        }
                        "compare" => Operation::compare_eq(
                            span,
                            address.clone(),
                            Value::Pattern(b(literal.clone())),
                        ),
                        "self copy" => Operation::memcpy(span, address.clone(), address.clone()),
                        "direct call" | "invoke" => {
                            let (callee, call_ty, _) = &targets[usize::from(case == "invoke")];
                            let output = builder
                                .append_operation(block, Operation::alloca(span, Type::unit()))
                                .unwrap();
                            Operation::call(
                                span,
                                Value::Function(*callee),
                                [address.clone(), output],
                                call_ty.clone(),
                            )
                        }
                        _ => unreachable!(),
                    };
                    if case == "invoke" {
                        let normal = builder.add_block();
                        let error = builder.add_block();
                        builder.set_terminator(
                            block,
                            Terminator::invoke(span, operation, normal, error),
                        );
                        builder.set_terminator(normal, Terminator::ret(span));
                        builder.set_terminator(error, Terminator::propagate_error(span));
                    } else {
                        builder.append_operation(block, operation);
                        builder.set_terminator(block, Terminator::ret(span));
                    }
                    let body = builder.finish_physical(env);
                    let roles = ValueRoles::derive(&body);
                    let (_, plan) = Analysis::of(
                        &body,
                        &roles,
                        &callees,
                        &program,
                        &session,
                        env,
                        false,
                        &FxHashSet::default(),
                    );
                    let Value::Register(id) = address else {
                        unreachable!()
                    };
                    assert_eq!(
                        plan.has_value(id),
                        if matches!(case, "direct call" | "invoke") {
                            pointer_slot
                        } else {
                            if aggregate {
                                matches!(
                                    case,
                                    "load"
                                        | "copy source"
                                        | "copy destination"
                                        | "move source"
                                        | "move destination"
                                )
                            } else {
                                case != "self copy"
                            }
                        },
                        "{case}, aggregate={aggregate}, pointer_slot={pointer_slot}"
                    );
                }
            }
        }
    }

    #[wasm_bindgen_test]
    fn wasm_codegen_selected_method_stores_keep_destination_addresses() {
        let mut session = CompilerSession::new();
        let module = session
            .compile(
                "trait Tag<Self> { fn tag(value: Self) -> int; } fn seed() {}",
                "selected_address_guard",
                Path::single_str("selected_address_guard"),
            )
            .unwrap()
            .module_id;
        let trait_id = session
            .expect_fresh_module(module)
            .get_trait_id(ustr("Tag"))
            .unwrap();
        let program = session.prepare_physical_program(module).unwrap();
        let env = session.module_env();
        let span = Location::new_synthesized();
        let ty = Type::function_by_val([int_type()], int_type());
        for selected in [false, true] {
            for (name, kind) in [
                ("store", OperationKind::Store),
                ("copy", OperationKind::Memcpy),
                ("move", OperationKind::Move),
            ] {
                let mut builder =
                    FunctionBuilder::new("selected_field".into(), CallResultConvention::NoValue);
                let destination = Value::Parameter(builder.add_parameter(
                    Type::tuple([ty, ty]),
                    ParameterKind::Parameter(ArgConvention::MutableRef),
                ));
                let block = builder.add_block();
                let source = if selected {
                    let dictionary = Value::Parameter(
                        builder.add_parameter(Type::unit(), ParameterKind::Dictionary),
                    );
                    builder
                        .append_operation(
                            block,
                            Operation::dict_entry(
                                span,
                                dictionary,
                                trait_id,
                                TraitDictionaryEntryIndex::from_index(0),
                                ty,
                            ),
                        )
                        .unwrap()
                } else {
                    Value::Parameter(
                        builder
                            .add_parameter(ty, ParameterKind::Parameter(ArgConvention::MutableRef)),
                    )
                };
                let source = if kind == OperationKind::Store {
                    // Store uses a materialized Load; copies and moves use the entry place.
                    builder
                        .append_operation(block, Operation::load(span, source))
                        .unwrap()
                } else {
                    source
                };
                let offset = Value::Constant(builder.add_constant(
                    int_type(),
                    LiteralValue::new_native(8_isize),
                    &env,
                ));
                let address = builder
                    .append_operation(
                        block,
                        Operation::address_offset(span, destination, offset, ty, None),
                    )
                    .unwrap();
                let operation = match kind {
                    OperationKind::Store => Operation::store(span, source, address.clone()),
                    OperationKind::Memcpy => Operation::memcpy(span, source, address.clone()),
                    OperationKind::Move => Operation::move_value(span, source, address.clone()),
                    _ => unreachable!(),
                };
                builder.append_operation(block, operation);
                builder.set_terminator(block, Terminator::ret(span));
                let body = builder.finish_physical(env);
                let roles = ValueRoles::derive(&body);
                let (_, plan) = Analysis::of(
                    &body,
                    &roles,
                    &FxHashMap::default(),
                    &program,
                    &session,
                    env,
                    false,
                    &FxHashSet::default(),
                );
                let Value::Register(id) = address else {
                    unreachable!()
                };
                assert_eq!(plan.has_value(id), !selected, "{name}, selected={selected}");
            }
        }
    }

    #[wasm_bindgen_test]
    fn wasm_codegen_metadata_load_keeps_its_deferred_producer() {
        let mut session = CompilerSession::new();
        let module = session
            .compile(
                "fn unused() {}",
                "metadata_guard",
                Path::single_str("metadata_guard"),
            )
            .unwrap()
            .module_id;
        let program = session.prepare_physical_program(module).unwrap();
        let env = session.module_env();
        let span = Location::new_synthesized();
        for (defer_store, defer_address) in [(true, false), (false, true), (false, false)] {
            let mut builder =
                FunctionBuilder::new("metadata_guard".into(), CallResultConvention::NoValue);
            let buffer = Value::Parameter(builder.add_parameter(
                buffer_type(int_type()),
                ParameterKind::Parameter(ArgConvention::Let),
            ));
            let input = Value::Parameter(
                builder.add_parameter(int_type(), ParameterKind::Parameter(ArgConvention::Let)),
            );
            let block = builder.add_block();
            // Use a runtime value so literal rematerialization does not replace store deferral.
            let input = builder
                .append_operation(block, Operation::load(span, input))
                .unwrap();
            let zero = Value::Constant(builder.add_constant(
                int_type(),
                LiteralValue::new_native(0_isize),
                &env,
            ));
            let slot = builder
                .append_operation(
                    block,
                    Operation::address_offset_place(span, buffer, zero.clone(), int_type()),
                )
                .unwrap();
            let base = builder
                .append_operation(block, Operation::load(span, slot))
                .unwrap();
            let index = if defer_address {
                builder
                    .append_operation(
                        block,
                        Operation::address_offset(
                            span,
                            base.clone(),
                            zero.clone(),
                            int_type(),
                            None,
                        ),
                    )
                    .unwrap()
            } else {
                let index = builder
                    .append_operation(block, Operation::alloca(span, int_type()))
                    .unwrap();
                builder
                    .append_operation(block, Operation::store(span, input.clone(), index.clone()));
                if !defer_store {
                    // Two writes prevent deferral, making this a metadata load that can disappear.
                    builder.append_operation(
                        block,
                        Operation::store(span, input.clone(), index.clone()),
                    );
                }
                index
            };
            let logical_index = builder
                .append_operation(block, Operation::load(span, index.clone()))
                .unwrap();
            builder.append_operation(
                block,
                Operation::address_offset_indexed(
                    span,
                    base,
                    zero,
                    logical_index.clone(),
                    int_type(),
                ),
            );
            builder.set_terminator(block, Terminator::ret(span));
            let body = builder.finish_physical(env);
            let roles = ValueRoles::derive(&body);
            let (analysis, plan) = Analysis::of(
                &body,
                &roles,
                &FxHashMap::default(),
                &program,
                &session,
                env,
                false,
                &FxHashSet::default(),
            );
            assert_eq!(
                plan.has_place(&index),
                defer_store,
                "fixture must exercise store deferral"
            );
            let Value::Register(index_id) = &index else {
                unreachable!()
            };
            assert_eq!(
                plan.has_value(*index_id),
                defer_address,
                "fixture must exercise address deferral"
            );
            let load = body
                .block(block)
                .operations()
                .iter()
                .find(|op| op.result_id().map(Value::Register).as_ref() == Some(&logical_index))
                .unwrap();
            assert_eq!(
                analysis.skips_metadata_load(load),
                !defer_store && !defer_address,
                "a metadata-only load must execute its deferred source"
            );
        }
    }
}
