// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Shared scalar-storage facts and conservative Wasm expression-tree plans.

use crate::{
    CompilerSession, FxHashMap, FxHashSet, define_id_type,
    mir::{
        BasicBlock, BlockId, Function, Operation, OperationKind, ParameterId, ParameterKind, Value,
        ValueId,
        pass::known_callee::KnownCallee,
        physical::program::ResolvedPhysicalProgram,
        role::{ValueRole, ValueRoles},
        site::OperationIndex,
        terminator::TerminatorKind,
    },
    module::{FunctionId, id::Id},
    wasm::abi::{CallAbi, Parameter as ParameterTransport, WasmFunctionId},
};

use super::{is_elided_stack_operation, scalar, wasm_intrinsic};

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

/// Dense facts shared by scalar storage assignment and expression-tree emission.
pub(super) struct Analysis {
    parameter_count: usize,
    register_count: usize,
    operation_bases: Vec<FlatOperationId>,
    addressed: Vec<bool>,
    intrinsics: Vec<Option<KnownCallee>>,
    comparison_fusions: Vec<Option<KnownCallee>>,
}

impl Analysis {
    pub(super) fn of(
        body: &Function,
        roles: &ValueRoles,
        callees: &FxHashMap<FunctionId, (WasmFunctionId, &CallAbi)>,
        program: &ResolvedPhysicalProgram<'_>,
        session: &CompilerSession,
        returns_direct_place: bool,
        no_op_stack_markers: &FxHashSet<ValueId>,
    ) -> (Self, Plan) {
        let layout = OperationLayout::of(body);
        let inputs = Inputs::of(
            body,
            roles,
            callees,
            program,
            session,
            returns_direct_place,
            &layout,
        );
        let comparison_fusions = comparison_fusions(body, &layout, &inputs);
        let plan = Plan::of(
            body,
            roles,
            &inputs,
            &comparison_fusions,
            &layout,
            no_op_stack_markers,
        );
        let analysis = Self {
            parameter_count: body.parameters().len(),
            register_count: roles.register_count(),
            operation_bases: layout.bases,
            addressed: inputs.addressed,
            intrinsics: inputs.intrinsics,
            comparison_fusions,
        };
        (analysis, plan)
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

    pub(super) fn comparison_fusion(&self, id: ValueId) -> Option<KnownCallee> {
        self.comparison_fusions
            .get(id.as_index())
            .copied()
            .flatten()
    }
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
        comparison_fusions: &[Option<KnownCallee>],
        layout: &OperationLayout,
        no_op_stack_markers: &FxHashSet<ValueId>,
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
            if inputs.is_addressed(&value, parameter_count, value_count)
                || comparison_fusions[id.as_index()].is_some()
            {
                continue;
            }
            let Some(consumer) = inputs.value_uses[index].one() else {
                continue;
            };
            if consumer.block != source.block
                || consumer.operation_id().as_index() <= source.operation_id().as_index()
                || !stackifiable_consumer(body, consumer)
            {
                continue;
            }
            let scalar_result = roles
                .get(&Value::Register(id), body.constants())
                .is_some_and(|role| {
                    matches!(&*role, ValueRole::VariantTag)
                        || matches!(&*role, ValueRole::Materialized(ty) if scalar(ty).is_ok())
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
                || !roles
                    .get(&value, body.constants())
                    .and_then(|role| role.place_pointee_type())
                    .is_some_and(|ty| scalar(&ty).is_ok())
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
                            !matches!(callee, KnownCallee::IntCmpCode | KnownCallee::FloatCmpCode)
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
                    Some(KnownCallee::IntCmpCode | KnownCallee::FloatCmpCode)
                ) && !fused_comparison_call(
                    block,
                    root_source.operation_id(),
                    comparison_fusions,
                ) {
                    // Materializing a comparison code reads both inputs twice. Keep its arguments
                    // in locals; adjacent predicate fusion has its own single-read path.
                    continue;
                }
                let ultimate_root =
                    group_ultimate_root[root_index].expect("non-empty expression group");
                let contiguous = (first.as_index()..root_index).all(|operation| {
                    ultimate_roots[operation] == Some(ultimate_root)
                        || is_neutral(
                            &block.operations()[operation - base.as_index()],
                            no_op_stack_markers,
                        )
                });
                accepted[root_index] = contiguous;
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
    One(Source),
    Two,
    Multiple,
    /// Emission may skip one of the uses, so the value cannot be deferred to its consumer.
    Elidable,
}

impl Uses {
    fn add(&mut self, source: Source) {
        *self = match *self {
            Self::None => Self::One(source),
            Self::One(_) => Self::Two,
            Self::Two | Self::Multiple => Self::Multiple,
            Self::Elidable => Self::Elidable,
        };
    }

    fn one(self) -> Option<Source> {
        match self {
            Self::One(source) => Some(source),
            Self::None | Self::Two | Self::Multiple | Self::Elidable => None,
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
}

impl Accesses {
    fn add(&mut self, access: Access) {
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
    value_uses: Vec<Uses>,
    value_definitions: Vec<Option<Source>>,
    definitions: Vec<Option<Source>>,
    place_roots: Vec<bool>,
    place_accesses: Vec<Accesses>,
    addressed: Vec<bool>,
    intrinsics: Vec<Option<KnownCallee>>,
}

impl Inputs {
    fn is_addressed(&self, value: &Value, parameter_count: usize, register_count: usize) -> bool {
        dense_value_index(value, parameter_count, register_count)
            .is_some_and(|id| self.addressed[id.as_index()])
    }

    fn intrinsic(&self, layout: &OperationLayout, source: Source) -> Option<KnownCallee> {
        self.intrinsics[layout.index(source).as_index()]
    }

    fn of(
        body: &Function,
        roles: &ValueRoles,
        callees: &FxHashMap<FunctionId, (WasmFunctionId, &CallAbi)>,
        program: &ResolvedPhysicalProgram<'_>,
        session: &CompilerSession,
        returns_direct_place: bool,
        layout: &OperationLayout,
    ) -> Self {
        let value_count = roles.register_count();
        let parameter_count = body.parameters().len();
        let place_count = parameter_count + value_count;
        let mut value_definitions = vec![None; value_count];
        let mut definitions = vec![None; value_count];
        let mut place_roots = vec![false; place_count];
        if returns_direct_place {
            for (index, parameter) in body.parameters().iter().enumerate() {
                if parameter.kind == ParameterKind::Return {
                    place_roots[index] = true;
                }
            }
        }

        let mut scan = OperandScan::new(body, roles, parameter_count, value_count);
        let mut intrinsics = vec![None; layout.operation_count];
        for block_id in body.blocks() {
            let block = body.block(block_id);
            for (operation, op) in block.operations().iter().enumerate() {
                let source = Source::from_index(block_id, operation);
                if let Some(id) = op.result_id() {
                    definitions[id.as_index()] = Some(source);
                    if matches!(op.kind, OperationKind::Alloca { .. }) && op.operands.is_empty() {
                        place_roots[parameter_count + id.as_index()] = true;
                    } else if matches!(
                        op.kind,
                        OperationKind::Load
                            | OperationKind::CompareEqual
                            | OperationKind::ExtractTag
                            | OperationKind::ExtractPayloadIndirection
                    ) {
                        value_definitions[id.as_index()] = Some(source);
                    }
                }
                let intrinsic = wasm_intrinsic(session, op);
                intrinsics[layout.index(source).as_index()] = intrinsic;
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
                    scan.operands(
                        operation,
                        source,
                        intrinsic,
                        call_abi(operation, intrinsic, callees, program),
                    );
                }
                TerminatorKind::Return => {
                    for (index, parameter) in body.parameters().iter().enumerate() {
                        if parameter.kind == ParameterKind::Return && place_roots[index] {
                            scan.place_accesses[index].add(Access {
                                source,
                                kind: AccessKind::Read,
                            });
                        }
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
        Self {
            value_uses: scan.value_uses,
            value_definitions,
            definitions,
            place_roots,
            place_accesses: scan.place_accesses,
            addressed: scan.addressed,
            intrinsics,
        }
    }
}

struct OperandScan<'a> {
    body: &'a Function,
    roles: &'a ValueRoles,
    parameter_count: usize,
    register_count: usize,
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
    ) -> Self {
        Self {
            body,
            roles,
            parameter_count,
            register_count,
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
        for (index, operand) in operation.operands.iter().enumerate() {
            self.operand(operand, source, classify_access(operation, index));
            if is_elidable_operand(operation, index) {
                self.elidable_operand(operand);
            }
            if observes_address(operation, index, intrinsic, call_abi, self.roles, self.body) {
                self.mark_addressed(operand);
            }
        }
    }

    fn elidable_operand(&mut self, operand: &Value) {
        if let Value::Register(id) = operand {
            self.value_uses[id.as_index()] = Uses::Elidable;
        }
    }

    fn operand(&mut self, operand: &Value, source: Source, kind: Option<AccessKind>) {
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
) -> bool {
    match &operation.kind {
        OperationKind::Load
        | OperationKind::Clear
        | OperationKind::Memcpy
        | OperationKind::Move
        | OperationKind::MoveBytes { .. }
        | OperationKind::CompareEqual => false,
        OperationKind::Store if index == 1 => false,
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

/// Whether emission consumes eligible scalar operands exactly once before performing effects.
///
/// This is deliberately an allow-list: adding a MIR operation cannot silently make deferred
/// producers sound without also documenting its emission contract here.
fn stackifiable_consumer(body: &Function, source: Source) -> bool {
    let block = body.block(source.block);
    if let Some(operation) = block.operations().get(source.operation_id().as_index()) {
        return stackifiable_operation(operation);
    }
    match &block.terminator().kind {
        TerminatorKind::CondBr { .. } | TerminatorKind::Return => true,
        TerminatorKind::Invoke { operation, .. } => stackifiable_operation(operation),
        _ => false,
    }
}

fn fused_comparison_call(
    block: &BasicBlock,
    operation: OperationIndex,
    comparison_fusions: &[Option<KnownCallee>],
) -> bool {
    block
        .operations()
        .get(operation.as_index() + 1)
        .and_then(Operation::result_id)
        .is_some_and(|id| comparison_fusions[id.as_index()].is_some())
}

/// Finds comparison-code calls whose fresh, unaliased output is tested immediately.
///
/// Adjacency keeps the comparison inputs live until the test is emitted. Requiring a fresh
/// `Alloca` output and exactly the call plus test uses permits omission of the materialized
/// comparison code without leaving observable stale memory behind.
fn comparison_fusions(
    body: &Function,
    layout: &OperationLayout,
    inputs: &Inputs,
) -> Vec<Option<KnownCallee>> {
    let mut fused = vec![None; inputs.value_uses.len()];
    for block_id in body.blocks() {
        let operations = body.block(block_id).operations();
        for (index, pair) in operations.windows(2).enumerate() {
            let [call, test] = pair else { unreachable!() };
            let Some(intrinsic @ (KnownCallee::IntCmpCode | KnownCallee::FloatCmpCode)) =
                inputs.intrinsics[layout.index(Source::from_index(block_id, index)).as_index()]
            else {
                continue;
            };
            let OperationKind::Call { ty, .. } = &call.kind else {
                continue;
            };
            if !ty.result_convention.has_result_place()
                || !matches!(test.kind, OperationKind::CompareEqual)
                || call.operands.len() != 4
                || test.operands.len() != 2
            {
                continue;
            }
            let output = &call.operands[3];
            let Value::Register(output_id) = output else {
                continue;
            };
            let Value::Pattern(pattern) = &test.operands[1] else {
                continue;
            };
            let fresh_output = inputs.definitions[output_id.as_index()].is_some_and(|source| {
                matches!(
                    body.block(source.block).operations()[source.operation_id().as_index()].kind,
                    OperationKind::Alloca { .. }
                )
            });
            if test.operands[0] != *output
                || !inputs.value_uses[output_id.as_index()].is_two()
                || !fresh_output
                || !matches!(pattern.as_primitive_ty::<isize>(), Some(-1..=1))
            {
                continue;
            }
            if let Some(result) = test.result_id() {
                fused[result.as_index()] = Some(intrinsic);
            }
        }
    }
    fused
}
