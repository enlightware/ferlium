// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Split local, non-escaping `TrivialCopy` products and variants into independent places.
//!
//! This changes storage, not values: mutable fields remain places, allocated at the original
//! lifetime boundary. Only static product projections, copies between participating products and
//! clears may observe a split product. Scalar fields retain their own identity and typed readers.
//! Whole-value readers, address arithmetic, opaque projections and managed products are excluded.
//!
//! A variant splits into a tag place, of the unit-only variant with the same cases, and one place
//! per distinct inline payload type. Storage is a function of the payload type rather than the
//! case, as in the variant's own union layout: a payload projection selects the active case, so
//! cases sharing a payload type may share its place. Shells, tag reads and payload projections may
//! observe a split variant. Copying or clearing one would have to select the active payload, so
//! those keep the variant whole.

use std::{collections::VecDeque, mem, ops::Range, rc::Rc};

use rustc_hash::FxHashMap;
use ustr::Ustr;

use super::{dataflow::field_index, dce};
use crate::{
    hir::value::{LiteralValue, VariantPayloadStorage},
    mir::{
        self, BlockId, Function, Operation, OperationKind, ValueId, edit::FunctionEdit,
        terminator::TerminatorKind, value::ConstantId,
    },
    module::{ModuleEnv, id::Id},
    std::value::{structural_variant, variant_payload_storage_for_payload_type},
    types::{
        r#type::{Type, TypeKind},
        type_properties::{TypePropertyEnv, concrete_type_is_trivial_copy},
    },
};

struct Node {
    ty: Type,
    /// Product fields, or the distinct payload types of a variant.
    children: Vec<usize>,
    leaves: Range<usize>,
    /// The tag leaf of a variant node.
    tag: Option<usize>,
    /// Whether the subtree contains a variant, whose copies would depend on its active case.
    has_variant: bool,
    /// Whether the node lies within a variant payload, whose initialization a new shell resets.
    in_payload: bool,
}

impl Node {
    fn is_leaf(&self) -> bool {
        self.children.is_empty() && self.tag.is_none()
    }
}

struct Shape {
    nodes: Vec<Node>,
    leaf_types: Vec<Type>,
}

// Bound compiler growth by field count, independently of byte layout. The node budget also
// bounds deeply nested products containing only one field at each level.
const MAX_LEAVES: usize = 64;
const MAX_NODES: usize = 256;

pub(super) enum Parts {
    Product(Vec<Type>),
    Variant { tag: Type, payloads: Vec<Type> },
}

/// Explicit ownership and native `TrivialCopy` contracts stay opaque: an opt-in promises that
/// the whole representation is copyable, not that each field is independently copyable.
pub(super) fn parts(mut ty: Type, env: ModuleEnv<'_>) -> Option<Parts> {
    let root = ty;
    loop {
        let kind = ty.data().clone();
        // Primitive allocations are common; reject them before querying native impls.
        if !matches!(
            kind,
            TypeKind::Tuple(_) | TypeKind::Record(_) | TypeKind::Variant(_) | TypeKind::Named(_)
        ) {
            return None;
        }
        if env.has_trivial_copy_impl(ty) {
            return None;
        }
        match kind {
            TypeKind::Tuple(fields) => {
                return (!fields.is_empty()).then_some(Parts::Product(fields));
            }
            TypeKind::Record(fields) => {
                return (!fields.is_empty())
                    .then(|| Parts::Product(fields.into_iter().map(|(_, ty)| ty).collect()));
            }
            TypeKind::Variant(_) => return variant_parts(root, env),
            TypeKind::Named(named) => {
                if env.type_def(named.def).has_custom_value_impl {
                    return None;
                }
                ty = named.instantiated_shape(&env);
            }
            _ => return None,
        }
    }
}

/// A unit-only variant is already a scalar tag. Indirect (recursive) payloads own storage.
fn variant_parts(ty: Type, env: ModuleEnv<'_>) -> Option<Parts> {
    let (_, cases) = structural_variant(ty, &env)?;
    let mut payloads = Vec::new();
    for (_, payload) in &cases {
        if *payload != Type::unit() && !payloads.contains(payload) {
            if variant_payload_storage_for_payload_type(ty, *payload, &env)
                != Some(VariantPayloadStorage::Inline)
            {
                return None;
            }
            payloads.push(*payload);
        }
    }
    if payloads.is_empty() {
        return None;
    }
    let tag = Type::variant(
        cases
            .into_iter()
            .map(|(name, _)| (name, Type::unit()))
            .collect::<Vec<_>>(),
    );
    Some(Parts::Variant { tag, payloads })
}

impl Shape {
    fn of(ty: Type, env: ModuleEnv<'_>) -> Option<Self> {
        let mut root_parts = Some(parts(ty, env)?);
        let mut shape = Self {
            nodes: Vec::new(),
            leaf_types: Vec::new(),
        };
        shape.nodes.push(Node {
            ty,
            children: Vec::new(),
            leaves: 0..0,
            tag: None,
            has_variant: false,
            in_payload: false,
        });
        // An iterative traversal avoids recursion in this pass and gives every subtree a
        // contiguous leaf range. Each node is visited twice, regardless of nesting depth.
        let mut pending = vec![(0, false)];
        while let Some((index, finished)) = pending.pop() {
            if finished {
                let node = &shape.nodes[index];
                let has_variant = node.tag.is_some()
                    || node
                        .children
                        .iter()
                        .any(|child| shape.nodes[*child].has_variant);
                let node = &mut shape.nodes[index];
                node.leaves.end = shape.leaf_types.len();
                node.has_variant = has_variant;
                continue;
            }
            shape.nodes[index].leaves.start = shape.leaf_types.len();
            pending.push((index, true));
            let parts = if index == 0 {
                root_parts.take()
            } else {
                parts(shape.nodes[index].ty, env)
            };
            let fields = match parts {
                Some(Parts::Product(fields)) => fields,
                Some(Parts::Variant { tag, payloads }) => {
                    if shape.leaf_types.len() == MAX_LEAVES {
                        return None;
                    }
                    shape.nodes[index].tag = Some(shape.leaf_types.len());
                    shape.leaf_types.push(tag);
                    payloads
                }
                None => {
                    if shape.leaf_types.len() == MAX_LEAVES {
                        return None;
                    }
                    shape.leaf_types.push(shape.nodes[index].ty);
                    continue;
                }
            };
            if fields.len() > MAX_NODES - shape.nodes.len() {
                return None;
            }
            let parent = &shape.nodes[index];
            let in_payload = parent.in_payload || parent.tag.is_some();
            let children: Vec<_> = fields
                .into_iter()
                .map(|ty| {
                    let child = shape.nodes.len();
                    shape.nodes.push(Node {
                        ty,
                        children: Vec::new(),
                        leaves: 0..0,
                        tag: None,
                        has_variant: false,
                        in_payload,
                    });
                    child
                })
                .collect();
            pending.extend(children.iter().rev().map(|child| (*child, false)));
            shape.nodes[index].children = children;
        }
        // Reject oversized shapes before the recursive ownership query: compact named types
        // can otherwise describe exponentially many structural fields.
        concrete_type_is_trivial_copy(ty, &env).then_some(shape)
    }
}

struct Shell {
    tag: Ustr,
    ty: Type,
    /// Candidates whose variant nodes this shell is stored into.
    roots: Vec<ValueId>,
    /// Used other than by being stored into a candidate variant node.
    opaque: bool,
}

struct Candidate {
    shape: Rc<Shape>,
    invalid: bool,
    copies: Vec<ValueId>,
    fields: Vec<ValueId>,
}

#[derive(Clone, Copy)]
struct Binding {
    root: ValueId,
    node: usize,
}

struct Projection {
    base: ValueId,
    field: Option<usize>,
    variant_payload: bool,
    ty: Type,
}

type Bindings = FxHashMap<ValueId, Option<Binding>>;

fn binding(value: &mir::Value, bindings: &Bindings) -> Option<Binding> {
    let mir::Value::Register(id) = value else {
        return None;
    };
    bindings.get(id).copied().flatten()
}

/// Borrow literal fields without evaluating or reconstructing their representations.
fn literal_fields<'a>(
    shape: &Shape,
    node: usize,
    literal: &'a LiteralValue,
) -> Option<Vec<&'a LiteralValue>> {
    let mut fields = Vec::new();
    let mut pending = vec![(node, literal)];
    while let Some((node, literal)) = pending.pop() {
        if shape.nodes[node].tag.is_some() {
            return None;
        }
        let children = &shape.nodes[node].children;
        if children.is_empty() {
            fields.push(literal);
        } else {
            let LiteralValue::Tuple(values) = literal else {
                return None;
            };
            if values.len() != children.len() {
                return None;
            }
            pending.extend(
                children
                    .iter()
                    .zip(values.iter())
                    .rev()
                    .map(|(node, value)| (*node, value)),
            );
        }
    }
    Some(fields)
}

/// Splits eligible local products. Analysis is linear in operands and projection/type nodes;
/// rewriting is additionally proportional to the fieldwise copies it emits. Copy dependencies
/// propagate rejection once per root/edge, rather than rescanning the function to a fixed point.
pub(crate) fn split_local_products(func: &Function, env: ModuleEnv<'_>) -> Option<Function> {
    let mut shapes = FxHashMap::<Type, Option<Rc<Shape>>>::default();
    let mut candidates = FxHashMap::<ValueId, Candidate>::default();
    let mut projections = FxHashMap::<ValueId, Projection>::default();
    let mut bindings = Bindings::default();
    // Concrete inline shells, by register: their case and constructed variant type.
    let mut shells = FxHashMap::<ValueId, Shell>::default();
    for block in func.blocks() {
        for operation in func.block(block).operations() {
            let Some(result) = operation.result_id() else {
                continue;
            };
            match operation.kind {
                OperationKind::Alloca { ty } => {
                    let shape = shapes
                        .entry(ty)
                        .or_insert_with(|| Shape::of(ty, env).map(Rc::new));
                    if let Some(shape) = shape {
                        candidates.insert(
                            result,
                            Candidate {
                                shape: shape.clone(),
                                invalid: false,
                                copies: Vec::new(),
                                fields: Vec::new(),
                            },
                        );
                        bindings.insert(
                            result,
                            Some(Binding {
                                root: result,
                                node: 0,
                            }),
                        );
                    }
                }
                OperationKind::Subfield {
                    ty,
                    variant_payload,
                    has_layout_witness: false,
                    ..
                } if operation.operands.len() == 2 => {
                    if let mir::Value::Register(base) = operation.operands[0] {
                        projections.insert(
                            result,
                            Projection {
                                base,
                                field: field_index(&operation.operands[1], func)
                                    .map(|i| i.as_index()),
                                variant_payload,
                                ty,
                            },
                        );
                    }
                }
                OperationKind::Variant {
                    tag,
                    ref metadata,
                    storage: Some(VariantPayloadStorage::Inline),
                    has_layout_witness: false,
                } if operation.operands.is_empty() => {
                    shells.insert(
                        result,
                        Shell {
                            tag,
                            ty: metadata.ty,
                            roots: Vec::new(),
                            opaque: false,
                        },
                    );
                }
                _ => {}
            }
        }
    }
    if candidates.is_empty() {
        return None;
    }

    // Definitions need not follow block order. Memoize an iterative walk so a long projection
    // chain is resolved once, including chains which do not originate at a candidate.
    for id in projections.keys().copied() {
        let mut current = id;
        let mut trail = Vec::new();
        while !bindings.contains_key(&current) {
            let Some(projection) = projections.get(&current) else {
                bindings.insert(current, None);
                break;
            };
            trail.push(current);
            current = projection.base;
        }
        let mut resolved = bindings[&current];
        for id in trail.into_iter().rev() {
            let projection = &projections[&id];
            resolved = resolved.and_then(|base| {
                let shape = &candidates[&base.root].shape;
                let node = &shape.nodes[base.node];
                // A payload projection selects the active case's payload by its type.
                let child = if projection.variant_payload {
                    node.tag?;
                    *node
                        .children
                        .iter()
                        .find(|child| shape.nodes[**child].ty == projection.ty)?
                } else {
                    node.tag.is_none().then_some(())?;
                    *node.children.get(projection.field?)?
                };
                (shape.nodes[child].ty == projection.ty).then_some(Binding {
                    root: base.root,
                    node: child,
                })
            });
            bindings.insert(id, resolved);
        }
    }

    for block in func.blocks() {
        let basic = func.block(block);
        for operation in basic.operations() {
            check_operation(operation, func, &bindings, &mut candidates, &mut shells);
        }
        if let TerminatorKind::Invoke { operation, .. } = &basic.terminator().kind {
            check_operation(operation, func, &bindings, &mut candidates, &mut shells);
            // Invoke operations are not expanded by the rewrite. Even if future MIR admits
            // fallible product operations, only their already-independent leaves may survive.
            for operand in &operation.operands {
                if let Some(place) = binding(operand, &bindings) {
                    let candidate = candidates.get_mut(&place.root).unwrap();
                    if !candidate.shape.nodes[place.node].is_leaf() {
                        candidate.invalid = true;
                    }
                }
            }
        } else {
            for value in basic.terminator().operands() {
                if let Some(place) = binding(value, &bindings) {
                    candidates.get_mut(&place.root).unwrap().invalid = true;
                }
                if let mir::Value::Register(id) = value
                    && let Some(shell) = shells.get_mut(id)
                {
                    shell.opaque = true;
                }
            }
        }
    }
    // A shell stored into split variants becomes a tag-only shell, so every other place it is
    // stored into must split too. A shell used otherwise keeps its variant type, and the variants
    // it initializes stay whole. Shared shells reject together, like copies.
    for shell in shells.values() {
        if shell.opaque {
            for root in &shell.roots {
                candidates.get_mut(root).unwrap().invalid = true;
            }
        }
        for pair in shell.roots.windows(2) {
            candidates.get_mut(&pair[0]).unwrap().copies.push(pair[1]);
            candidates.get_mut(&pair[1]).unwrap().copies.push(pair[0]);
        }
    }
    reject_families(&mut candidates);
    if candidates
        .values()
        .any(|candidate| candidate.shape.nodes[0].has_variant)
    {
        for root in uninitialized_payload_reads(func, &bindings, &candidates) {
            candidates.get_mut(&root).unwrap().invalid = true;
        }
        reject_families(&mut candidates);
    }
    if candidates.is_empty() {
        return None;
    }
    // Shared shells were rejected together, so a shell's first root decides for all of them.
    let tag_shells: FxHashMap<ValueId, (Ustr, Type)> = shells
        .into_iter()
        .filter_map(|(id, shell)| {
            let root = shell.roots.first()?;
            let shape = &candidates.get(root)?.shape;
            let node = shape.nodes.iter().find(|node| node.ty == shell.ty)?;
            Some((id, (shell.tag, shape.leaf_types[node.tag?])))
        })
        .collect();

    let mut edit = FunctionEdit::new(func.clone());
    // Borrow keys from the original pool/its field literals. Append new typed leaves with hash
    // interning instead of a linear pool search for every field of a large literal product.
    let mut field_constants = None;
    // Use original allocation order, not hash iteration order, for deterministic value identities.
    for block in func.blocks() {
        for operation in func.block(block).operations() {
            if let Some(candidate) = operation.result_id().and_then(|id| candidates.get_mut(&id)) {
                candidate.fields = candidate
                    .shape
                    .leaf_types
                    .iter()
                    .map(|_| edit.new_value())
                    .collect();
            }
        }
    }
    for block in func.blocks() {
        let original = mem::take(&mut edit.block_mut(block).operations);
        let mut operations = Vec::with_capacity(original.len());
        for operation in original {
            if let Some(candidate) = operation.result_id().and_then(|id| candidates.get(&id)) {
                for (field, ty) in candidate.fields.iter().zip(&candidate.shape.leaf_types) {
                    let mut allocation = Operation::alloca(operation.span, *ty);
                    allocation.assign_result_id(Some(*field));
                    operations.push(allocation);
                }
                continue;
            }
            if let Some(&(tag, tag_ty)) = operation.result_id().and_then(|id| tag_shells.get(&id)) {
                let mut shell = Operation::variant(
                    operation.span,
                    tag,
                    tag_ty,
                    Type::unit(),
                    Some(VariantPayloadStorage::Inline),
                    None,
                    None,
                );
                shell.assign_result_id(operation.result_id());
                operations.push(shell);
                continue;
            }
            if operation.kind == OperationKind::Store
                && let Some(place) = binding(&operation.operands[1], &bindings)
                && let Some(candidate) = candidates.get(&place.root)
                && let Some(tag) = candidate.shape.nodes[place.node].tag
            {
                operations.push(Operation::store(
                    operation.span,
                    operation.operands[0].clone(),
                    mir::Value::Register(candidate.fields[tag]),
                ));
                continue;
            }
            if matches!(operation.kind, OperationKind::Subfield { .. })
                && operation
                    .result_id()
                    .and_then(|id| bindings.get(&id))
                    .copied()
                    .flatten()
                    .is_some_and(|place| candidates.contains_key(&place.root))
            {
                continue;
            }
            if operation.kind == OperationKind::Store
                && let Some(place) = binding(&operation.operands[1], &bindings)
                && let Some(candidate) = candidates.get(&place.root)
                && !candidate.shape.nodes[place.node].is_leaf()
            {
                let mir::Value::Constant(id) = operation.operands[0] else {
                    unreachable!("only literal product stores qualify")
                };
                let literals = literal_fields(
                    &candidate.shape,
                    place.node,
                    &func.constant(id).representation,
                )
                .unwrap();
                let field_constants = field_constants.get_or_insert_with(|| {
                    func.constants()
                        .iter()
                        .enumerate()
                        .map(|(index, constant)| {
                            (
                                (constant.ty, &constant.representation),
                                ConstantId::from_index(index),
                            )
                        })
                        .collect::<FxHashMap<_, _>>()
                });
                let range = candidate.shape.nodes[place.node].leaves.clone();
                for ((literal, ty), field) in literals
                    .into_iter()
                    .zip(&candidate.shape.leaf_types[range.clone()])
                    .zip(&candidate.fields[range])
                {
                    let literal = *field_constants
                        .entry((*ty, literal))
                        .or_insert_with(|| edit.append_constant(*ty, literal.clone(), &env));
                    operations.push(Operation::store(
                        operation.span,
                        mir::Value::Constant(literal),
                        mir::Value::Register(*field),
                    ));
                }
                continue;
            }
            if matches!(
                operation.kind,
                OperationKind::Memcpy | OperationKind::Move | OperationKind::Clear
            ) && let Some(place) = binding(&operation.operands[0], &bindings)
                && let Some(candidate) = candidates.get(&place.root)
                && !candidate.shape.nodes[place.node].is_leaf()
            {
                let source = &candidate.fields[candidate.shape.nodes[place.node].leaves.clone()];
                if operation.kind == OperationKind::Clear {
                    operations.extend(
                        source
                            .iter()
                            .map(|id| Operation::clear(operation.span, mir::Value::Register(*id))),
                    );
                } else {
                    let target = binding(&operation.operands[1], &bindings).unwrap();
                    let destination = &candidates[&target.root];
                    let destination =
                        &destination.fields[destination.shape.nodes[target.node].leaves.clone()];
                    // Equal-typed subtrees of non-recursive products are either identical or
                    // disjoint. Thus fieldwise copies preserve overlap and self-move behavior.
                    for (source, destination) in source.iter().zip(destination) {
                        let source = mir::Value::Register(*source);
                        let destination = mir::Value::Register(*destination);
                        operations.push(if operation.kind == OperationKind::Move {
                            Operation::move_value(operation.span, source, destination)
                        } else {
                            Operation::memcpy(operation.span, source, destination)
                        });
                    }
                }
                continue;
            }
            operations.push(operation);
        }
        edit.block_mut(block).operations = operations;
    }
    edit.visit_operands_mut(|operand| {
        if let Some(place) = binding(operand, &bindings)
            && let Some(candidate) = candidates.get(&place.root)
        {
            let node = &candidate.shape.nodes[place.node];
            // Only tag reads still observe a whole variant; they read its tag place.
            let leaf = node.tag.unwrap_or_else(|| {
                debug_assert!(node.is_leaf(), "all whole-product uses were rewritten");
                node.leaves.start
            });
            *operand = mir::Value::Register(candidate.fields[leaf]);
        }
    });
    let split = edit.finish(env);
    // A variant whose tag nothing reads after branch forwarding leaves a tag place that is only
    // written. Removing it here, once, avoids running the cleanup on every function each round.
    if candidates
        .values()
        .any(|candidate| candidate.shape.nodes[0].has_variant)
    {
        return Some(dce::remove_discarded_trivial_copy_results(&split, env).unwrap_or(split));
    }
    Some(split)
}

/// Rejects invalid candidates together with every candidate linked to them by a copy or shell.
fn reject_families(candidates: &mut FxHashMap<ValueId, Candidate>) {
    let mut rejected: VecDeque<_> = candidates
        .iter()
        .filter_map(|(id, c)| c.invalid.then_some(*id))
        .collect();
    while let Some(root) = rejected.pop_front() {
        let copies = mem::take(&mut candidates.get_mut(&root).unwrap().copies);
        for other in copies {
            let candidate = candidates.get_mut(&other).unwrap();
            if !candidate.invalid {
                candidate.invalid = true;
                rejected.push_back(other);
            }
        }
    }
    candidates.retain(|_, candidate| !candidate.invalid);
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Effect {
    Read,
    Kill,
    Write,
}

/// The ranges of tracked bits an operation reads, deinitializes and initializes, in that order.
fn payload_effects(
    operation: &Operation,
    bindings: &Bindings,
    candidates: &FxHashMap<ValueId, Candidate>,
    bases: &FxHashMap<ValueId, usize>,
    mut effect: impl FnMut(ValueId, Range<usize>, Effect),
) {
    let last = operation.operands.len().wrapping_sub(1);
    for pass in [Effect::Read, Effect::Kill, Effect::Write] {
        for (index, operand) in operation.operands.iter().enumerate() {
            let Some(place) = binding(operand, bindings) else {
                continue;
            };
            let Some(&base) = bases.get(&place.root) else {
                continue;
            };
            let role = match (&operation.kind, index) {
                (OperationKind::Load | OperationKind::CompareEqual, 0) => Effect::Read,
                (OperationKind::Memcpy, 0) => Effect::Read,
                (OperationKind::Move, 0) if pass == Effect::Kill => Effect::Kill,
                (OperationKind::Move, 0) => Effect::Read,
                (OperationKind::Memcpy | OperationKind::Move | OperationKind::Store, 1) => {
                    Effect::Write
                }
                (OperationKind::Clear, 0) => Effect::Kill,
                (OperationKind::Call { .. }, index) if index == last => Effect::Write,
                (OperationKind::Call { .. }, index) if index > 0 => Effect::Read,
                _ => continue,
            };
            let node = &candidates[&place.root].shape.nodes[place.node];
            // A shell store initializes only the tag, which is not tracked.
            if role == pass && node.tag.is_none() {
                effect(
                    place.root,
                    base + node.leaves.start..base + node.leaves.end,
                    role,
                );
            }
        }
    }
}

/// Roots whose split payload would be read where it is not definitely initialized.
///
/// A whole variant's tag proves which payload is initialized; once split, each payload place must
/// be initialized on every path to its reads by itself, as for any other local. This is a forward
/// must-analysis over the tracked payload leaves of all variant candidates. A payload only known
/// initialized from a tag test therefore keeps its variant whole. An invoke's result is
/// conservatively not counted, as it is initialized only on its normal edge.
fn uninitialized_payload_reads(
    func: &Function,
    bindings: &Bindings,
    candidates: &FxHashMap<ValueId, Candidate>,
) -> Vec<ValueId> {
    let mut bases = FxHashMap::<ValueId, usize>::default();
    let mut payload = Vec::<bool>::new();
    for (root, candidate) in candidates {
        let shape = &candidate.shape;
        if !shape.nodes[0].has_variant {
            continue;
        }
        let base = payload.len();
        bases.insert(*root, base);
        payload.resize(base + shape.leaf_types.len(), false);
        for node in shape.nodes.iter().filter(|node| node.tag.is_some()) {
            for child in &node.children {
                for leaf in shape.nodes[*child].leaves.clone() {
                    payload[base + leaf] = true;
                }
            }
        }
    }
    let words = payload.len().div_ceil(64);
    let set = |state: &mut [u64], range: Range<usize>, value: bool| {
        for bit in range {
            if value {
                state[bit / 64] |= 1 << (bit % 64);
            } else {
                state[bit / 64] &= !(1 << (bit % 64));
            }
        }
    };
    let initialized = |state: &[u64], range: Range<usize>| {
        range
            .into_iter()
            .all(|bit| !payload[bit] || state[bit / 64] & (1 << (bit % 64)) != 0)
    };
    let block_count = func.blocks().count();
    let mut predecessors = vec![Vec::new(); block_count];
    for block in func.blocks() {
        for successor in func.block(block).terminator().successors() {
            predecessors[successor.as_index()].push(block);
        }
    }
    let operations = |block| {
        let basic = func.block(block);
        let invoked = match &basic.terminator().kind {
            TerminatorKind::Invoke { operation, .. } => Some(operation),
            _ => None,
        };
        basic
            .operations()
            .iter()
            .map(|op| (op, false))
            .chain(invoked.map(|op| (op, true)))
    };
    let transfer = |state: &mut Vec<u64>, block, mut read: Option<&mut Vec<ValueId>>| {
        for (operation, invoked) in operations(block) {
            payload_effects(
                operation,
                bindings,
                candidates,
                &bases,
                |root, range, effect| match effect {
                    Effect::Read => {
                        if let Some(rejected) = read.as_deref_mut()
                            && !initialized(state, range)
                        {
                            rejected.push(root);
                        }
                    }
                    Effect::Kill => set(state, range, false),
                    Effect::Write if invoked => {}
                    Effect::Write => set(state, range, true),
                },
            );
        }
    };
    // Must-analysis: every block but the entry starts at the top and only loses bits.
    let entry = func.entry();
    let mut outputs = vec![vec![u64::MAX; words]; block_count];
    let mut changed = true;
    while changed {
        changed = false;
        for block in func.blocks() {
            let mut state = if block == entry {
                vec![0; words]
            } else {
                meet(&predecessors[block.as_index()], &outputs, words)
            };
            transfer(&mut state, block, None);
            if state != outputs[block.as_index()] {
                outputs[block.as_index()] = state;
                changed = true;
            }
        }
    }
    let mut rejected = Vec::new();
    for block in func.blocks() {
        let mut state = if block == entry {
            vec![0; words]
        } else {
            meet(&predecessors[block.as_index()], &outputs, words)
        };
        transfer(&mut state, block, Some(&mut rejected));
    }
    rejected
}

fn meet(predecessors: &[BlockId], outputs: &[Vec<u64>], words: usize) -> Vec<u64> {
    let mut state = vec![u64::MAX; words];
    for predecessor in predecessors {
        for (word, output) in state.iter_mut().zip(&outputs[predecessor.as_index()]) {
            *word &= output;
        }
    }
    state
}

fn check_operation(
    operation: &Operation,
    func: &Function,
    bindings: &Bindings,
    candidates: &mut FxHashMap<ValueId, Candidate>,
    shells: &mut FxHashMap<ValueId, Shell>,
) {
    let source = operation
        .operands
        .first()
        .and_then(|v| binding(v, bindings));
    let destination = operation.operands.get(1).and_then(|v| binding(v, bindings));
    let copy = matches!(operation.kind, OperationKind::Memcpy | OperationKind::Move)
        && operation.operands.len() == 2;
    let product_copy = copy
        && source.zip(destination).is_some_and(|(a, b)| {
            let a = &candidates[&a.root].shape.nodes[a.node];
            let b = &candidates[&b.root].shape.nodes[b.node];
            !a.is_leaf() && a.ty == b.ty
        });
    if product_copy {
        let (a, b) = source.zip(destination).unwrap();
        candidates.get_mut(&a.root).unwrap().copies.push(b.root);
        candidates.get_mut(&b.root).unwrap().copies.push(a.root);
    }
    // A shell stored into a variant node: the shell's only admitted use.
    let shell_store = (operation.kind == OperationKind::Store)
        .then(|| {
            let mir::Value::Register(id) = operation.operands[0] else {
                return None;
            };
            let place = destination?;
            let node = &candidates[&place.root].shape.nodes[place.node];
            let shell = shells.get(&id)?;
            (node.tag.is_some() && shell.ty == node.ty).then_some((id, place.root))
        })
        .flatten();
    if let Some((shell, root)) = shell_store {
        shells.get_mut(&shell).unwrap().roots.push(root);
    }
    for (index, operand) in operation.operands.iter().enumerate() {
        if let mir::Value::Register(id) = operand
            && !(index == 0 && shell_store.is_some())
            && let Some(shell) = shells.get_mut(id)
        {
            shell.opaque = true;
        }
        let Some(place) = binding(operand, bindings) else {
            continue;
        };
        let node = &candidates[&place.root].shape.nodes[place.node];
        let allowed = if node.is_leaf() {
            match operation.kind {
                OperationKind::Load
                | OperationKind::CompareEqual
                | OperationKind::Clear
                | OperationKind::ExtractTag => index == 0,
                // Storing a shell resets its payload's initialization, but a split shell store
                // writes only the tag; valid MIR reads no payload before rewriting it, so only
                // this query could observe the difference.
                OperationKind::IsInitialized => index == 0 && !node.in_payload,
                OperationKind::Store => index == 1,
                OperationKind::Memcpy | OperationKind::Move => copy,
                OperationKind::Call { .. } => index > 0,
                _ => false,
            }
        } else {
            match operation.kind {
                OperationKind::Subfield { .. } => {
                    index == 0
                        && operation
                            .result_id()
                            .and_then(|id| bindings.get(&id))
                            .copied()
                            .flatten()
                            .is_some()
                }
                OperationKind::Memcpy | OperationKind::Move => product_copy && !node.has_variant,
                OperationKind::Store if node.tag.is_some() => index == 1 && shell_store.is_some(),
                OperationKind::Store => {
                    index == 1
                        && matches!(&operation.operands[0], mir::Value::Constant(id)
                        if literal_fields(&candidates[&place.root].shape, place.node, &func.constant(*id).representation).is_some())
                }
                OperationKind::Clear => index == 0 && !node.has_variant,
                OperationKind::ExtractTag => index == 0 && node.tag.is_some(),
                _ => false,
            }
        };
        if !allowed {
            candidates.get_mut(&place.root).unwrap().invalid = true;
        }
    }
}

#[cfg(test)]
mod tests {
    use rustc_hash::FxHashSet;

    use super::{MAX_LEAVES, MAX_NODES, Shape, split_local_products};
    use crate::{
        CompilerSession, Location, MirOptimization,
        hir::{
            function::ArgConvention,
            value::{LiteralValue, Value as RuntimeValue, VariantPayloadStorage},
        },
        mir::{
            BlockId, Function, Operation, OperationKind, ParameterKind, Value,
            builder::FunctionBuilder,
            edit::FunctionEdit,
            terminator::{Terminator, TerminatorKind},
            verify::verify_function,
        },
        module::Path,
        std::{
            logic::bool_type,
            math::{Float, int_type},
            string::string_type,
        },
        types::r#type::Type,
    };

    fn field(
        builder: &mut FunctionBuilder,
        block: BlockId,
        base: Value,
        index: isize,
        ty: Type,
        aggregate: Type,
        session: &CompilerSession,
    ) -> Value {
        let index = Value::Constant(builder.add_constant(
            int_type(),
            LiteralValue::new_native(index),
            &session.module_env(),
        ));
        builder
            .append_operation(
                block,
                Operation::product_subfield(
                    Location::new_synthesized(),
                    base,
                    index,
                    ty,
                    aggregate,
                    [],
                ),
            )
            .unwrap()
    }

    /// A local `None | Some((int,))` written on both branches of a condition and read after the
    /// join. With `tag_tested`, the second branch writes `None` and the payload is read only after
    /// testing the tag.
    fn joined_variant(tag_tested: bool, session: &CompilerSession) -> (Function, Type) {
        let env = session.module_env();
        let span = Location::new_synthesized();
        let payload = Type::tuple(vec![int_type()]);
        let ty = Type::variant(vec![
            ("None".into(), Type::unit()),
            ("Some".into(), payload),
        ]);
        let mut builder = FunctionBuilder::new("joined_variant".into(), Default::default());
        let condition = Value::Parameter(
            builder.add_parameter(bool_type(), ParameterKind::Parameter(ArgConvention::Let)),
        );
        let output = Value::Parameter(builder.add_parameter(int_type(), ParameterKind::Return));
        let entry = builder.add_block();
        let branches = [builder.add_block(), builder.add_block()];
        let join = builder.add_block();
        let cell = builder
            .append_operation(entry, Operation::alloca(span, ty))
            .unwrap();
        let taken = builder
            .append_operation(entry, Operation::load(span, condition))
            .unwrap();
        builder.set_terminator(
            entry,
            Terminator::cond_br(span, taken, branches[0], branches[1]),
        );
        let zero = Value::Constant(builder.add_constant(
            int_type(),
            LiteralValue::new_native(0isize),
            &env,
        ));
        let payload_field = |builder: &mut FunctionBuilder, block| {
            let place = builder
                .append_operation(
                    block,
                    Operation::variant_payload(span, cell.clone(), zero.clone(), payload, None),
                )
                .unwrap();
            field(builder, block, place, 0, int_type(), payload, session)
        };
        for (index, block) in branches.into_iter().enumerate() {
            let tag = if tag_tested && index == 1 {
                "None"
            } else {
                "Some"
            };
            let shell_ty = if tag == "None" { Type::unit() } else { payload };
            let shell = builder
                .append_operation(
                    block,
                    Operation::variant(
                        span,
                        tag.into(),
                        ty,
                        shell_ty,
                        Some(VariantPayloadStorage::Inline),
                        None,
                        None,
                    ),
                )
                .unwrap();
            builder.append_operation(block, Operation::store(span, shell, cell.clone()));
            if tag == "Some" {
                let place = payload_field(&mut builder, block);
                let value = Value::Constant(builder.add_constant(
                    int_type(),
                    LiteralValue::new_native(7isize + index as isize),
                    &env,
                ));
                builder.append_operation(block, Operation::store(span, value, place));
            }
            builder.set_terminator(block, Terminator::goto(span, join));
        }
        let read = if tag_tested {
            let read = builder.add_block();
            let exit = builder.add_block();
            let tag = builder
                .append_operation(join, Operation::extract_tag(span, cell.clone()))
                .unwrap();
            builder.set_terminator(
                join,
                Terminator::switch_variant(span, tag, vec![("Some".into(), read)], exit),
            );
            builder.append_operation(exit, Operation::store(span, zero.clone(), output.clone()));
            builder.set_terminator(exit, Terminator::ret(span));
            read
        } else {
            join
        };
        let place = payload_field(&mut builder, read);
        let value = builder
            .append_operation(read, Operation::load(span, place))
            .unwrap();
        builder.append_operation(read, Operation::store(span, value, output));
        builder.set_terminator(read, Terminator::ret(span));
        (builder.finish(env), ty)
    }

    #[test]
    fn variants_split_into_tag_and_payload_places() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let (original, ty) = joined_variant(false, &session);
        let split = split_local_products(&original, env).expect("the variant must split");
        verify_function(&split, env);
        let allocated: Vec<_> = split
            .blocks()
            .flat_map(|block| split.block(block).operations())
            .filter_map(|op| match op.kind {
                OperationKind::Alloca { ty } => Some(ty),
                _ => None,
            })
            .collect();
        // The tag would be stored in a unit-only variant place.
        let tag = Type::variant(vec![
            ("None".into(), Type::unit()),
            ("Some".into(), Type::unit()),
        ]);
        assert!(
            !allocated.contains(&ty),
            "the variant is no longer stored whole"
        );
        assert!(
            !allocated.contains(&tag)
                && !split
                    .blocks()
                    .flat_map(|block| split.block(block).operations())
                    .any(|op| matches!(op.kind, OperationKind::Variant { .. })),
            "an unread tag place is removed together with its shells"
        );
        assert!(
            allocated.contains(&int_type()),
            "its payload has a scalar place"
        );
        assert!(
            !split
                .blocks()
                .flat_map(|block| split.block(block).operations())
                .any(|op| matches!(op.kind, OperationKind::Subfield { .. })),
            "payload projections resolve to the split places"
        );
    }

    #[test]
    fn payloads_initialized_only_under_a_tag_test_keep_their_variant() {
        // Once split, nothing relates the payload place to the tag that proves it initialized.
        let session = CompilerSession::new();
        let (original, _) = joined_variant(true, &session);
        assert!(split_local_products(&original, session.module_env()).is_none());
    }

    #[test]
    fn payload_initialization_queries_keep_their_variant() {
        // A new shell resets its payload's initialization; a split shell store writes the tag only.
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        let payload = Type::tuple(vec![int_type()]);
        let ty = Type::variant(vec![
            ("None".into(), Type::unit()),
            ("Some".into(), payload),
        ]);
        let mut builder = FunctionBuilder::new("requeried_payload".into(), Default::default());
        let output = Value::Parameter(builder.add_parameter(bool_type(), ParameterKind::Return));
        let entry = builder.add_block();
        let cell = builder
            .append_operation(entry, Operation::alloca(span, ty))
            .unwrap();
        let zero = Value::Constant(builder.add_constant(
            int_type(),
            LiteralValue::new_native(0isize),
            &env,
        ));
        let payload_field = |builder: &mut FunctionBuilder| {
            let shell = builder
                .append_operation(
                    entry,
                    Operation::variant(
                        span,
                        "Some".into(),
                        ty,
                        payload,
                        Some(VariantPayloadStorage::Inline),
                        None,
                        None,
                    ),
                )
                .unwrap();
            builder.append_operation(entry, Operation::store(span, shell, cell.clone()));
            let place = builder
                .append_operation(
                    entry,
                    Operation::variant_payload(span, cell.clone(), zero.clone(), payload, None),
                )
                .unwrap();
            field(builder, entry, place, 0, int_type(), payload, &session)
        };
        let first = payload_field(&mut builder);
        let seven = Value::Constant(builder.add_constant(
            int_type(),
            LiteralValue::new_native(7isize),
            &env,
        ));
        builder.append_operation(entry, Operation::store(span, seven, first));
        let second = payload_field(&mut builder);
        let initialized = builder
            .append_operation(entry, Operation::is_initialized(span, second))
            .unwrap();
        builder.append_operation(entry, Operation::store(span, initialized, output));
        builder.set_terminator(entry, Terminator::ret(span));
        let original = builder.finish(env);
        assert!(split_local_products(&original, env).is_none());
    }

    #[test]
    fn nested_products_preserve_field_identity_copies_and_lifetimes() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        let inner = Type::record(vec![
            ("count".into(), int_type()),
            ("ready".into(), bool_type()),
        ]);
        let ty = Type::tuple(vec![int_type(), inner]);
        let mut builder = FunctionBuilder::new("nested_products".into(), Default::default());
        let output = Value::Parameter(builder.add_parameter(int_type(), ParameterKind::Return));
        let entry = builder.add_block();
        let source = builder
            .append_operation(entry, Operation::alloca(span, ty))
            .unwrap();
        let destination = builder
            .append_operation(entry, Operation::alloca(span, ty))
            .unwrap();
        let first = field(
            &mut builder,
            entry,
            source.clone(),
            0,
            int_type(),
            ty,
            &session,
        );
        let repeated = field(
            &mut builder,
            entry,
            source.clone(),
            0,
            int_type(),
            ty,
            &session,
        );
        let nested = field(&mut builder, entry, source.clone(), 1, inner, ty, &session);
        let second = field(
            &mut builder,
            entry,
            nested.clone(),
            0,
            int_type(),
            inner,
            &session,
        );
        let ready = field(&mut builder, entry, nested, 1, bool_type(), inner, &session);
        let number = Value::Constant(builder.add_constant(
            int_type(),
            LiteralValue::new_native(13isize),
            &env,
        ));
        let boolean = Value::Constant(builder.add_constant(
            bool_type(),
            LiteralValue::new_native(true),
            &env,
        ));
        for place in [first, repeated, second] {
            builder.append_operation(entry, Operation::store(span, number.clone(), place));
        }
        builder.append_operation(entry, Operation::store(span, boolean, ready));
        let literal = Value::Constant(builder.add_constant(
            ty,
            LiteralValue::new_tuple(vec![
                LiteralValue::new_native(17isize),
                LiteralValue::new_tuple(vec![
                    LiteralValue::new_native(23isize),
                    LiteralValue::new_native(false),
                ]),
            ]),
            &env,
        ));
        builder.append_operation(entry, Operation::store(span, literal, source.clone()));
        let marker = builder
            .append_operation(entry, Operation::stack_save(span))
            .unwrap();
        builder.append_operation(
            entry,
            Operation::memcpy(span, source.clone(), destination.clone()),
        );
        builder.append_operation(entry, Operation::clear(span, source));
        builder.append_operation(
            entry,
            Operation::move_value(span, destination.clone(), destination.clone()),
        );
        let projected = field(
            &mut builder,
            entry,
            destination,
            0,
            int_type(),
            ty,
            &session,
        );
        let value = builder
            .append_operation(entry, Operation::load(span, projected))
            .unwrap();
        builder.append_operation(entry, Operation::store(span, value, output));
        builder.append_operation(entry, Operation::stack_restore(span, marker));
        builder.set_terminator(entry, Terminator::ret(span));
        let original = builder.finish(env);
        let split = split_local_products(&original, env).unwrap();
        verify_function(&split, env);
        let operations = split.block(entry).operations();
        assert!(
            !operations
                .iter()
                .any(|op| matches!(op.kind, OperationKind::Subfield { .. }))
        );
        assert_eq!(
            operations
                .iter()
                .filter(|op| matches!(op.kind, OperationKind::Alloca { .. }))
                .count(),
            6
        );
        let stores: Vec<_> = operations
            .iter()
            .filter(|op| op.kind == OperationKind::Store)
            .collect();
        assert_eq!(
            stores[0].operands[1], stores[1].operands[1],
            "repeated projections must share one field"
        );
        for (store, expected) in stores[4..6].iter().zip([17isize, 23]) {
            let Value::Constant(id) = store.operands[0] else {
                panic!("a literal field stays literal")
            };
            assert_eq!(
                split.constant(id).representation.as_primitive_ty::<isize>(),
                Some(&expected)
            );
        }
        assert_eq!(
            operations
                .iter()
                .filter(|op| op.kind == OperationKind::Memcpy)
                .count(),
            3
        );
        assert_eq!(
            operations
                .iter()
                .filter(|op| op.kind == OperationKind::Clear)
                .count(),
            3
        );
        for operation in operations
            .iter()
            .filter(|op| op.kind == OperationKind::Move)
        {
            assert_eq!(
                operation.operands[0], operation.operands[1],
                "self-moves remain self-moves"
            );
        }
        let marker = operations
            .iter()
            .position(|op| op.kind == OperationKind::StackSave)
            .unwrap();
        assert!(
            operations[marker..]
                .iter()
                .all(|op| !matches!(op.kind, OperationKind::Alloca { .. })),
            "field storage keeps the original lifetime boundary"
        );
        assert!(split_local_products(&split, env).is_none());
    }

    #[test]
    fn opaque_uses_reject_complete_copy_families() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        let ty = Type::tuple(vec![int_type(), int_type()]);
        for opaque in ["whole read", "foreign copy", "field address", "invoke copy"] {
            let mut builder = FunctionBuilder::new(opaque.into(), Default::default());
            let parameter = Value::Parameter(
                builder.add_parameter(ty, ParameterKind::Parameter(ArgConvention::Let)),
            );
            let entry = builder.add_block();
            let roots: Vec<_> = (0..3)
                .map(|_| {
                    builder
                        .append_operation(entry, Operation::alloca(span, ty))
                        .unwrap()
                })
                .collect();
            for index in 0..2 {
                let place = field(
                    &mut builder,
                    entry,
                    roots[0].clone(),
                    index,
                    int_type(),
                    ty,
                    &session,
                );
                let value = Value::Constant(builder.add_constant(
                    int_type(),
                    LiteralValue::new_native(7isize),
                    &env,
                ));
                builder.append_operation(entry, Operation::store(span, value, place));
            }
            for pair in roots.windows(2) {
                builder.append_operation(
                    entry,
                    Operation::memcpy(span, pair[0].clone(), pair[1].clone()),
                );
            }
            match opaque {
                "whole read" => {
                    builder.append_operation(entry, Operation::load(span, roots[2].clone()));
                }
                "foreign copy" => {
                    builder.append_operation(
                        entry,
                        Operation::memcpy(span, parameter, roots[2].clone()),
                    );
                }
                "field address" => {
                    let place = field(
                        &mut builder,
                        entry,
                        roots[2].clone(),
                        0,
                        int_type(),
                        ty,
                        &session,
                    );
                    // A raw address projection cannot rely on fields remaining contiguous.
                    let zero = Value::Constant(builder.add_constant(
                        int_type(),
                        LiteralValue::new_native(0isize),
                        &env,
                    ));
                    builder.append_operation(
                        entry,
                        Operation::address_offset(span, place, zero, int_type(), None),
                    );
                }
                "invoke copy" => {}
                _ => unreachable!(),
            }
            builder.set_terminator(entry, Terminator::ret(span));
            let original = builder.finish(env);
            let original = if opaque == "invoke copy" {
                // This is deliberately outside today's verified MIR: ensure future fallible
                // product operations cannot accidentally pass the non-Invoke rewrite.
                let mut edit = FunctionEdit::new(original);
                let normal = edit.add_block(Terminator::ret(span));
                let error = edit.add_block(Terminator::ret(span));
                edit.block_mut(entry).terminator = Terminator::invoke(
                    span,
                    Operation::memcpy(span, roots[0].clone(), roots[2].clone()),
                    normal,
                    error,
                );
                edit.finish_unverified()
            } else {
                original
            };
            assert!(split_local_products(&original, env).is_none(), "{opaque}");
        }
    }

    #[test]
    fn managed_products_retain_storage() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        let ty = Type::tuple(vec![int_type(), string_type()]);
        let mut builder = FunctionBuilder::new("managed_product".into(), Default::default());
        let entry = builder.add_block();
        let root = builder
            .append_operation(entry, Operation::alloca(span, ty))
            .unwrap();
        field(&mut builder, entry, root, 0, int_type(), ty, &session);
        builder.set_terminator(entry, Terminator::ret(span));
        let original = builder.finish(env);
        assert!(split_local_products(&original, env).is_none());
        assert!(Shape::of(Type::tuple(vec![int_type(); MAX_LEAVES]), env).is_some());
        assert!(Shape::of(Type::tuple(vec![int_type(); MAX_LEAVES + 1]), env).is_none());
        // Interned types can describe exponentially many fields without an equally large source.
        let mut exponentially_nested = int_type();
        for _ in 0..20 {
            exponentially_nested = Type::tuple(vec![exponentially_nested; 2]);
        }
        assert!(Shape::of(exponentially_nested, env).is_none());
        let mut deeply_nested = int_type();
        for _ in 0..MAX_NODES {
            deeply_nested = Type::tuple(vec![deeply_nested]);
        }
        assert!(Shape::of(deeply_nested, env).is_none());
    }

    #[test]
    fn split_fields_preserve_physical_execution_through_calls() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Disabled);
        let module = session
            .compile(
                "#[inline(never)]
                 fn add(x: int, y: int) -> int { x + y }
                 pub fn compute(n: int) -> int {
                     let mut p = (n, (2, 3));
                     p.1.0 = add(p.0, p.1.1);
                     add(p.1.0, p.1.1)
                 }
                 fn g(x: float, y: float) -> float { let p = (x, y); p.0 * p.1 }
                 pub fn f(a: float, b: float) -> float { g(a, b) * b - a }",
                "split_execution",
                Path::single_str("split_execution"),
            )
            .unwrap()
            .module_id;
        let entry = session
            .expect_fresh_module(module)
            .get_local_function_id("compute".into())
            .unwrap();
        for optimization in [MirOptimization::Disabled, MirOptimization::Enabled] {
            session.set_physical_mir_optimization(optimization);
            let (value, _) = session
                .run_physical_mir_entry_profiled(module, entry, vec![RuntimeValue::native(7isize)])
                .unwrap();
            assert_eq!(value.into_primitive_ty::<isize>().unwrap(), 13);
        }
        let original = session
            .mir_artifacts_for(module, MirOptimization::Disabled)
            .unwrap()
            .get(entry)
            .unwrap();
        let env = session
            .modules()
            .env_for(session.expect_fresh_module(module));
        let split = split_local_products(original, env).expect("fixture must actually split");
        let alloca_ids = |body: &Function| -> FxHashSet<_> {
            body.blocks()
                .flat_map(|block| {
                    body.block(block)
                        .operations()
                        .iter()
                        .filter(|op| matches!(op.kind, OperationKind::Alloca { .. }))
                        .map(|op| op.result_id().unwrap())
                })
                .collect()
        };
        let original_allocas = alloca_ids(original);
        let fields: FxHashSet<_> = alloca_ids(&split)
            .difference(&original_allocas)
            .copied()
            .collect();
        assert!(
            split.blocks().any(|block| {
                let block = split.block(block);
                let invoked = match &block.terminator().kind {
                    TerminatorKind::Invoke { operation, .. } => Some(operation),
                    _ => None,
                };
                block.operations().iter().chain(invoked).any(|op| {
                    matches!(op.kind, OperationKind::Call { .. })
                        && op.operands.iter().skip(1).any(
                            |value| matches!(value, Value::Register(id) if fields.contains(id)),
                        )
                })
            }),
            "retained call must read a split field directly"
        );
        // Also retain the original inlined-product float case end to end, after splitting.
        session.set_mir_optimization(MirOptimization::Enabled);
        let entry = session
            .expect_fresh_module(module)
            .get_local_function_id("f".into())
            .unwrap();
        let (value, _) = session
            .run_physical_mir_entry_profiled(
                module,
                entry,
                vec![
                    RuntimeValue::native(Float::new(2.0).unwrap()),
                    RuntimeValue::native(Float::new(3.0).unwrap()),
                ],
            )
            .unwrap();
        assert_eq!(
            value.into_primitive_ty::<Float>().unwrap().into_inner(),
            16.0
        );
        let rendered = session.emit_physical_mir_module(module).unwrap();
        let body = rendered
            .split("fn f(")
            .nth(1)
            .unwrap()
            .split("\nfn ")
            .next()
            .unwrap();
        assert_eq!(body.matches("raw_float_is_finite").count(), 1, "{body}");
    }
}
