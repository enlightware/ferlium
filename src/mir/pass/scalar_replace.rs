// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Split local, non-escaping `TrivialCopy` products and variants into independent places.
//!
//! This changes storage, not values: mutable fields remain places, allocated at the original
//! lifetime boundary. Only static product projections, copies between participating products and
//! clears may observe a split product. Scalar fields retain their own identity and typed readers.
//! Whole-value readers, address arithmetic, opaque projections and managed products are excluded.
//!
//! A separate mode splits local aggregates owning managed fields, including inline variants.
//! Their fields keep their clones, drops and projections. Structural drops are spliced first;
//! known-tag forwarding then exposes conditional payload lifetimes. A nested product cloned as a
//! whole stays whole. Rejected splits roll back their cleanup expansion; see
//! [`split_managed_local_products`].
//!
//! A variant splits into a tag place, of the unit-only variant with the same cases, and one place
//! per distinct inline payload type. Storage is a function of the payload type rather than the
//! case, as in the variant's own union layout: a payload projection selects the active case, so
//! cases sharing a payload type may share its place. Shells, tag reads and payload projections may
//! observe a split variant. Copying or clearing one would have to select the active payload, so
//! those keep the variant whole.

use std::{collections::VecDeque, mem, ops::Range, rc::Rc};

use rustc_hash::{FxHashMap, FxHashSet};
use ustr::Ustr;

use super::{
    OptimizationStage, branch_forward,
    dataflow::{field_index, resolve_dictionary_callee},
    dce, inline,
    site::{OperationIndex, OperationSite},
    stack_region,
};
use crate::{
    hir::value::{LiteralValue, VariantPayloadStorage},
    mir::{
        self, BlockId, Function, Operation, OperationKind, ValueId, edit::FunctionEdit,
        terminator::TerminatorKind,
    },
    module::{FunctionId, ModuleEnv, id::Id},
    std::value::{structural_variant, variant_payload_storage_for_payload_type},
    types::{
        effects::no_effects,
        r#type::{CallImplType, CallResultConvention, FnType, Type, TypeKind},
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

enum Parts {
    Product(Vec<Type>),
    Variant { tag: Type, payloads: Vec<Type> },
}

/// Explicit ownership and native `TrivialCopy` contracts stay opaque: an opt-in promises that
/// the whole representation is copyable, not that each field is independently copyable.
fn parts(mut ty: Type, env: ModuleEnv<'_>) -> Option<Parts> {
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
    /// A `TrivialCopy` shape, or with `managed`, a shape owning managed fields. Nested nodes of
    /// a type in `whole` are leaves.
    fn of(ty: Type, env: ModuleEnv<'_>, managed: bool, whole: &FxHashSet<Type>) -> Option<Self> {
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
            } else if whole.contains(&shape.nodes[index].ty) {
                None
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
        let trivial_copy = concrete_type_is_trivial_copy(ty, &env);
        let accepted = if managed { !trivial_copy } else { trivial_copy };
        accepted.then_some(shape)
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
    match split(
        func,
        env,
        None,
        &FxHashSet::default(),
        &FxHashSet::default(),
        &FxHashSet::default(),
    ) {
        Split::Done(split) => Some(split),
        Split::Unchanged | Split::Expand(_, _) | Split::Rejected(_) | Split::Reshape(_) => None,
    }
}

/// Splits local aggregates owning managed fields, including inline variant payloads, so that
/// each field's lifetime is a whole local.
///
/// A whole product is only dropped through its structural destructor, which is spliced first:
/// the drop becomes one initialization-aware drop per field, which the split then gives to each
/// field's local, as physical drop elaboration does for a partially initialized product. Each
/// splice removes one level of nesting, so the number of splices is bounded by the shape depth.
///
/// A nested product cloned as a whole, such as an element copied into `Some`, stays one local:
/// clone borrowing needs its whole lifetime in one place, while splitting it would need a clone
/// per field. Which products stay whole is a function-wide choice by type, made on the original
/// body and grown only, so it is bounded by the types in the function.
pub(crate) fn split_managed_local_products(
    func: &Function,
    env: ModuleEnv<'_>,
    stage: OptimizationStage<'_>,
) -> Option<Function> {
    let mut current: Option<Function> = None;
    let mut expanded_roots = FxHashSet::default();
    let mut excluded = FxHashSet::default();
    let mut whole = FxHashSet::default();
    for _ in 0..MAX_NODES {
        let source = current.as_ref().unwrap_or(func);
        match split(source, env, Some(stage), &excluded, &expanded_roots, &whole) {
            Split::Done(split) => return Some(split),
            // Splices are made only for products otherwise accepted; discard them if the split
            // still fails, as they only grow the body.
            Split::Unchanged => return None,
            Split::Rejected(roots) => {
                excluded.extend(roots);
                expanded_roots.clear();
                current = None;
            }
            Split::Reshape(types) => {
                whole.extend(types);
                expanded_roots.clear();
                current = None;
            }
            Split::Expand(drops, roots) => {
                expanded_roots.extend(roots);
                let expanded = expand_drops(source, &drops, env, stage)?;
                // A spliced destructor leaves its unit result cell, frame bracket and unread
                // dictionary entries in front of its tag test; branch forwarding needs them gone.
                let expanded = dce::remove_dead_storage(&expanded).unwrap_or(expanded);
                let expanded =
                    stack_region::remove_redundant_stack_markers(&expanded).unwrap_or(expanded);
                let expanded = dce::remove_dead_trivial_results(&expanded).unwrap_or(expanded);
                current =
                    Some(branch_forward::forward_variant_branches(&expanded).unwrap_or(expanded));
            }
        }
    }
    None
}

enum Split {
    Unchanged,
    /// Retry without these roots: their expanded cleanup cannot survive a failed split.
    Rejected(Vec<ValueId>),
    /// Whole-product drops to splice, and their roots, before those products can split.
    Expand(Vec<OperationSite>, Vec<ValueId>),
    /// Retry with nested products of these types kept whole.
    Reshape(FxHashSet<Type>),
    Done(Function),
}

/// The structural destructor a drop names, and its hidden evidence operands: a function, or a
/// method of a static dictionary.
fn destructor(
    operation: &Operation,
    definitions: &FxHashMap<ValueId, &Operation>,
    env: ModuleEnv<'_>,
) -> Option<(FunctionId, Vec<mir::Value>)> {
    let (callee, mut evidence) = resolve_dictionary_callee(
        &operation.operands[1],
        &|id| definitions.get(&id).copied(),
        env,
    )?;
    evidence.extend_from_slice(&operation.operands[2..]);
    Some((callee, evidence))
}

/// Splices the structural destructor of each drop at `drops`. Its field drops leave every managed
/// field uninitialized, as the whole drop did; the `TrivialCopy` fields keep their state, which only
/// an initialization query could observe, and the managed split admits none.
fn expand_drops(
    func: &Function,
    drops: &[OperationSite],
    env: ModuleEnv<'_>,
    stage: OptimizationStage<'_>,
) -> Option<Function> {
    let definitions = definitions(func);
    let mut expansions = Vec::with_capacity(drops.len());
    for &site in drops {
        let operation = &func.block(site.block).operations()[site.index.as_index()];
        let OperationKind::Drop { ty } = operation.kind else {
            unreachable!("only drops are expanded")
        };
        let (callee, evidence) = destructor(operation, &definitions, env)?;
        let template = inline::cleanup_template(stage.body(callee)?, ty, env)?;
        expansions.push((site, callee, evidence, template));
    }
    let mut edit = FunctionEdit::new(func.clone());
    // Later sites of a block first: a splice moves the operations after it to a new block,
    // leaving the earlier ones in place. Sites arrive in operation order.
    for (site, callee, mut arguments, template) in expansions.into_iter().rev() {
        let (block, index) = (site.block, site.index.as_index());
        let operation = edit.block_mut(block).operations[index].clone();
        let OperationKind::Drop { ty } = operation.kind else {
            unreachable!("only drops are expanded")
        };
        let span = operation.span;
        let target = operation.operands[0].clone();
        arguments.push(target.clone());
        let call = Operation::call(
            span,
            mir::Value::Function(callee),
            arguments,
            CallImplType::new(
                FnType::new_mut_resolved([(ty, true)], Type::unit(), no_effects()),
                CallResultConvention::NoValue,
            ),
        );
        edit.block_mut(block)
            .operations
            .splice(index..=index, [call]);
        inline::expand_cleanup(&mut edit, &template, callee.module, block, index, env);
    }
    edit.merge_blocks_into_predecessors();
    edit.reorder_blocks_in_reverse_postorder();
    Some(edit.finish_unverified())
}

fn definitions(func: &Function) -> FxHashMap<ValueId, &Operation> {
    func.blocks()
        .flat_map(|block| func.block(block).operations())
        .filter_map(|operation| Some((operation.result_id()?, operation)))
        .collect()
}

fn split(
    func: &Function,
    env: ModuleEnv<'_>,
    managed: Option<OptimizationStage<'_>>,
    excluded: &FxHashSet<ValueId>,
    expanded_roots: &FxHashSet<ValueId>,
    whole: &FxHashSet<Type>,
) -> Split {
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
                    let shape = shapes.entry(ty).or_insert_with(|| {
                        Shape::of(ty, env, managed.is_some(), whole).map(Rc::new)
                    });
                    if let Some(shape) = shape
                        && !excluded.contains(&result)
                    {
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
        return Split::Unchanged;
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

    let definitions = managed.map(|_| definitions(func));
    // A whole managed product is dropped only through a structural destructor whose body is known.
    let expandable = |operation: &Operation| {
        let (Some(stage), Some(definitions)) = (managed, &definitions) else {
            return false;
        };
        destructor(operation, definitions, env)
            .is_some_and(|(callee, _)| stage.body(callee).is_some())
    };
    let mut expanded = Vec::new();
    let mut kept_whole = FxHashSet::default();
    for block in func.blocks() {
        let basic = func.block(block);
        for (index, operation) in basic.operations().iter().enumerate() {
            if check_operation(
                operation,
                func,
                &bindings,
                &mut candidates,
                &mut shells,
                &mut kept_whole,
                managed.is_some(),
                &expandable,
            ) {
                expanded.push(OperationSite {
                    block,
                    index: OperationIndex::from_index(index),
                });
            }
        }
        if let TerminatorKind::Invoke { operation, .. } = &basic.terminator().kind {
            check_operation(
                operation,
                func,
                &bindings,
                &mut candidates,
                &mut shells,
                &mut kept_whole,
                managed.is_some(),
                &expandable,
            );
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
    if !kept_whole.is_empty() {
        return Split::Reshape(kept_whole);
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
    // Rejected roots must not postpone the final initialization/lifetime proof when
    // their speculative drops are the only expansions left in the worklist.
    let mut roots_to_expand = Vec::new();
    expanded.retain(|site| {
        binding(
            &func.block(site.block).operations()[site.index.as_index()].operands[0],
            &bindings,
        )
        .is_some_and(|place| {
            if candidates.contains_key(&place.root) {
                roots_to_expand.push(place.root);
                true
            } else {
                false
            }
        })
    });
    if expanded.is_empty()
        && candidates
            .values()
            .any(|candidate| candidate.shape.nodes[0].has_variant)
    {
        for root in
            uninitialized_payload_reads(func, &bindings, &candidates, managed.is_some(), env)
        {
            candidates.get_mut(&root).unwrap().invalid = true;
        }
        reject_families(&mut candidates);
    }
    let rejected: Vec<_> = expanded_roots
        .iter()
        .filter(|root| !candidates.contains_key(root))
        .copied()
        .collect();
    if !rejected.is_empty() {
        return Split::Rejected(rejected);
    }
    if candidates.is_empty() {
        return Split::Unchanged;
    }
    if !expanded.is_empty() {
        return Split::Expand(expanded, roots_to_expand);
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
                for leaf in candidate.shape.nodes[place.node].leaves.clone() {
                    if managed.is_some() && leaf != tag {
                        operations.push(Operation::clear(
                            operation.span,
                            mir::Value::Register(candidate.fields[leaf]),
                        ));
                    }
                }
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
                let range = candidate.shape.nodes[place.node].leaves.clone();
                for ((literal, ty), field) in literals
                    .into_iter()
                    .zip(&candidate.shape.leaf_types[range.clone()])
                    .zip(&candidate.fields[range])
                {
                    let literal = edit.add_constant(*ty, literal.clone(), &env);
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
        return Split::Done(
            dce::remove_discarded_trivial_copy_results(&split, env).unwrap_or(split),
        );
    }
    Split::Done(split)
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
    if let Some(root) = operation.result_id()
        && let Some(&base) = bases.get(&root)
    {
        effect(
            root,
            base..base + candidates[&root].shape.leaf_types.len(),
            Effect::Kill,
        );
    }
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
                (OperationKind::Memcpy | OperationKind::Clone { .. }, 0) => Effect::Read,
                (OperationKind::Move, 0) if pass == Effect::Kill => Effect::Kill,
                (OperationKind::Move, 0) => Effect::Read,
                (
                    OperationKind::Memcpy
                    | OperationKind::Move
                    | OperationKind::Store
                    | OperationKind::Clone { .. },
                    1,
                ) => Effect::Write,
                (OperationKind::Clear | OperationKind::Drop { .. }, 0) => Effect::Kill,
                (OperationKind::ExtractTag, 0) => Effect::Read,
                (OperationKind::Call { .. }, index)
                    if Some(index) == operation.call_result_place_index() =>
                {
                    Effect::Write
                }
                // The callee, a function value, is read in place like the arguments.
                (OperationKind::Call { .. }, _) => Effect::Read,
                _ => continue,
            };
            let node = &candidates[&place.root].shape.nodes[place.node];
            if let Some(tag) = node.tag {
                if operation.kind == OperationKind::Store && index == 1 {
                    if pass == Effect::Kill {
                        effect(
                            place.root,
                            base + node.leaves.start..base + node.leaves.end,
                            Effect::Kill,
                        );
                    } else if pass == Effect::Write {
                        effect(place.root, base + tag..base + tag + 1, Effect::Write);
                    }
                } else if operation.kind == OperationKind::ExtractTag && pass == Effect::Read {
                    effect(place.root, base + tag..base + tag + 1, Effect::Read);
                }
            } else if role == pass {
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
/// initialized from a tag test therefore keeps its variant whole. Tags must also be initialized
/// before expanded cleanup reads them. Shell stores reset payload initialization, and a separate
/// may-analysis rejects resets that could discard live ownership. An invoke's result is
/// conservatively not counted, as it is initialized only on its normal edge.
fn uninitialized_payload_reads(
    func: &Function,
    bindings: &Bindings,
    candidates: &FxHashMap<ValueId, Candidate>,
    managed: bool,
    env: ModuleEnv<'_>,
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
            payload[base + node.tag.unwrap()] = true;
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
    if !managed {
        return rejected;
    }
    // A shell resets its union payload. After splitting, do not clear a managed local
    // that can still own a value. In particular, a tag-dependent drop at a join may
    // need control-flow specialization before this independent-place proof succeeds. The same
    // may-live facts must show that stack restoration and exits leave no owned payload behind.
    let managed: Vec<bool> = {
        let mut managed = vec![false; payload.len()];
        for (root, base) in &bases {
            for (leaf, ty) in candidates[root].shape.leaf_types.iter().enumerate() {
                managed[base + leaf] = !concrete_type_is_trivial_copy(*ty, &env);
            }
        }
        managed
    };
    if !managed.iter().any(|managed| *managed) {
        return rejected;
    }
    let preserving: FxHashMap<_, _> = bases
        .keys()
        .map(|&root| (root, stack_region::restores_preserving_alloca(func, root)))
        .collect();
    let may_transfer = |state: &mut Vec<u64>, block, mut rejected: Option<&mut Vec<ValueId>>| {
        for (index, (operation, _)) in operations(block).enumerate() {
            if operation.kind == OperationKind::StackRestore {
                let site = OperationSite {
                    block,
                    index: OperationIndex::from_index(index),
                };
                for (&root, &base) in &bases {
                    if !preserving[&root].contains(&site) {
                        let range = base..base + candidates[&root].shape.leaf_types.len();
                        if let Some(rejected) = rejected.as_deref_mut()
                            && range
                                .clone()
                                .any(|bit| managed[bit] && state[bit / 64] & (1 << (bit % 64)) != 0)
                        {
                            rejected.push(root);
                        }
                        set(state, range, false);
                    }
                }
            }
            if operation.kind == OperationKind::Store
                && let Some(place) = binding(&operation.operands[1], bindings)
                && let Some(&base) = bases.get(&place.root)
                && candidates[&place.root].shape.nodes[place.node]
                    .tag
                    .is_some()
                && let Some(rejected) = rejected.as_deref_mut()
                && candidates[&place.root].shape.nodes[place.node]
                    .leaves
                    .clone()
                    .any(|leaf| {
                        let bit = base + leaf;
                        managed[bit] && state[bit / 64] & (1 << (bit % 64)) != 0
                    })
            {
                rejected.push(place.root);
            }
            payload_effects(
                operation,
                bindings,
                candidates,
                &bases,
                |_, range, effect| match effect {
                    Effect::Read => {}
                    Effect::Kill => set(state, range, false),
                    Effect::Write => set(state, range, true),
                },
            );
        }
        if func.block(block).terminator().successors().next().is_none()
            && let Some(rejected) = rejected.as_deref_mut()
        {
            for (&root, &base) in &bases {
                if (base..base + candidates[&root].shape.leaf_types.len())
                    .any(|bit| managed[bit] && state[bit / 64] & (1 << (bit % 64)) != 0)
                {
                    rejected.push(root);
                }
            }
        }
    };
    let union = |predecessors: &[BlockId], outputs: &[Vec<u64>]| {
        let mut state = vec![0; words];
        for predecessor in predecessors {
            for (word, output) in state.iter_mut().zip(&outputs[predecessor.as_index()]) {
                *word |= output;
            }
        }
        state
    };
    let mut outputs = vec![vec![0; words]; block_count];
    let mut changed = true;
    while changed {
        changed = false;
        for block in func.blocks() {
            let mut state = union(&predecessors[block.as_index()], &outputs);
            may_transfer(&mut state, block, None);
            if state != outputs[block.as_index()] {
                outputs[block.as_index()] = state;
                changed = true;
            }
        }
    }
    for block in func.blocks() {
        let mut state = union(&predecessors[block.as_index()], &outputs);
        may_transfer(&mut state, block, Some(&mut rejected));
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

/// Rejects the candidates `operation` observes other than as admitted, and returns whether it is
/// a whole-product drop of a `managed` candidate, admitted on condition of being `expandable`.
#[allow(clippy::too_many_arguments)]
fn check_operation(
    operation: &Operation,
    func: &Function,
    bindings: &Bindings,
    candidates: &mut FxHashMap<ValueId, Candidate>,
    shells: &mut FxHashMap<ValueId, Shell>,
    kept_whole: &mut FxHashSet<Type>,
    managed: bool,
    expandable: &dyn Fn(&Operation) -> bool,
) -> bool {
    let mut expands = false;
    let source = operation
        .operands
        .first()
        .and_then(|v| binding(v, bindings));
    let destination = operation.operands.get(1).and_then(|v| binding(v, bindings));
    let copy = matches!(operation.kind, OperationKind::Memcpy | OperationKind::Move)
        && operation.operands.len() == 2;
    // Both sides must be split: a root keeps the fields of a type kept whole when nested, so equal
    // types alone do not give equal shapes. A product copied into such a leaf stays whole.
    let product_copy = copy
        && source.zip(destination).is_some_and(|(a, b)| {
            let a = &candidates[&a.root].shape.nodes[a.node];
            let b = &candidates[&b.root].shape.nodes[b.node];
            !a.is_leaf() && !b.is_leaf() && a.ty == b.ty
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
                // this query could observe the difference. A spliced destructor leaves the
                // `TrivialCopy` fields of a managed product initialized, which it would observe.
                OperationKind::IsInitialized => !managed && index == 0 && !node.in_payload,
                OperationKind::Store => index == 1,
                OperationKind::Memcpy | OperationKind::Move => copy,
                // A call reads its callee, a function value, in place like its arguments.
                OperationKind::Call { .. } => true,
                // A managed field keeps its ownership operations and its own representation.
                OperationKind::Clone { .. } => managed && index <= 1,
                OperationKind::Drop { .. } => managed && index == 0,
                OperationKind::Subfield {
                    variant_payload: false,
                    ..
                } => managed && index == 0,
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
                OperationKind::Drop { .. } if managed && index == 0 && expandable(operation) => {
                    expands = true;
                    true
                }
                // A nested product cloned as a whole keeps its own clone, as a leaf.
                OperationKind::Clone { .. } if managed && index <= 1 && place.node != 0 => {
                    kept_whole.insert(node.ty);
                    false
                }
                _ => false,
            }
        };
        if !allowed {
            candidates.get_mut(&place.root).unwrap().invalid = true;
        }
    }
    expands
}

#[cfg(test)]
mod tests {
    use rustc_hash::FxHashSet;

    use ustr::ustr;

    use super::{MAX_LEAVES, MAX_NODES, Shape, split_local_products, split_managed_local_products};
    use crate::{
        CompilerSession, ExecutionTarget, Location, MirOptimization,
        hir::{
            function::ArgConvention,
            value::{LiteralValue, Value as RuntimeValue, VariantPayloadStorage},
        },
        mir::{
            BlockId, Function, Operation, OperationKind, ParameterKind, Value,
            builder::FunctionBuilder,
            edit::FunctionEdit,
            pass::{OptimizationStage, SemanticCallees},
            terminator::Terminator,
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
        let condition = Value::Parameter(builder.add_parameter(bool_type(), ParameterKind::Value));
        let output = Value::Parameter(builder.add_parameter(int_type(), ParameterKind::Return));
        let entry = builder.add_block();
        let branches = [builder.add_block(), builder.add_block()];
        let join = builder.add_block();
        let cell = builder
            .append_operation(entry, Operation::alloca(span, ty))
            .unwrap();
        let taken = condition.clone();
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
                builder.add_parameter(ty, ParameterKind::Place(ArgConvention::Let)),
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
        let shape = |ty| Shape::of(ty, env, false, &FxHashSet::default());
        assert!(shape(Type::tuple(vec![int_type(); MAX_LEAVES])).is_some());
        assert!(shape(Type::tuple(vec![int_type(); MAX_LEAVES + 1])).is_none());
        // Interned types can describe exponentially many fields without an equally large source.
        let mut exponentially_nested = int_type();
        for _ in 0..20 {
            exponentially_nested = Type::tuple(vec![exponentially_nested; 2]);
        }
        assert!(shape(exponentially_nested).is_none());
        let mut deeply_nested = int_type();
        for _ in 0..MAX_NODES {
            deeply_nested = Type::tuple(vec![deeply_nested]);
        }
        assert!(shape(deeply_nested).is_none());
    }

    #[test]
    fn a_split_root_is_not_copied_into_a_product_kept_whole() {
        // Cloning `x` into `outer.0` keeps `(string, string)` whole when nested, while the root
        // `local` of that type would still split; moving it whole into `moved.0` then needs one
        // representation on both sides.
        let mut session = CompilerSession::new();
        let module_id = session
            .compile_for(
                ExecutionTarget::Mir,
                "fn pair(x: (string, string)) -> (string, string) { x }
                 fn text(x: string) -> string { x }",
                "kept_whole",
                Path::single_str("kept_whole"),
            )
            .unwrap()
            .module_id;
        let module = session.expect_fresh_module(module_id);
        let artifacts = session
            .mir_artifacts_for(module_id, MirOptimization::Disabled)
            .unwrap();
        let clone_callee = |name: &str| {
            let body = artifacts
                .get(module.get_local_function_id(ustr(name)).unwrap())
                .unwrap();
            body.blocks()
                .flat_map(|block| body.block(block).operations())
                .find(|operation| matches!(operation.kind, OperationKind::Clone { .. }))
                .unwrap()
                .operands[2]
                .clone()
        };
        let (pair_clone, text_clone) = (clone_callee("pair"), clone_callee("text"));
        let env = session.modules().env_for(&module);
        let span = Location::new_synthesized();
        let pair = Type::tuple(vec![string_type(), string_type()]);
        let outer = Type::tuple(vec![pair, int_type()]);
        let mut builder = FunctionBuilder::new("kept_whole".into(), Default::default());
        let x =
            Value::Parameter(builder.add_parameter(pair, ParameterKind::Place(ArgConvention::Let)));
        let entry = builder.add_block();
        let [cloned, moved] = [outer; 2].map(|ty| {
            builder
                .append_operation(entry, Operation::alloca(span, ty))
                .unwrap()
        });
        let local = builder
            .append_operation(entry, Operation::alloca(span, pair))
            .unwrap();
        let target = field(&mut builder, entry, cloned, 0, pair, outer, &session);
        builder.append_operation(
            entry,
            Operation::clone_value(span, x.clone(), target, pair_clone, pair),
        );
        for index in 0..2 {
            let source = field(
                &mut builder,
                entry,
                x.clone(),
                index,
                string_type(),
                pair,
                &session,
            );
            let target = field(
                &mut builder,
                entry,
                local.clone(),
                index,
                string_type(),
                pair,
                &session,
            );
            builder.append_operation(
                entry,
                Operation::clone_value(span, source, target, text_clone.clone(), string_type()),
            );
        }
        let target = field(&mut builder, entry, moved, 0, pair, outer, &session);
        builder.append_operation(entry, Operation::move_value(span, local, target));
        builder.set_terminator(entry, Terminator::ret(span));
        let original = builder.finish(env);
        let stage = OptimizationStage::Semantic(SemanticCallees::new(&session, None));
        if let Some(split) = split_managed_local_products(&original, env, stage) {
            verify_function(&split, env);
            let moves = split
                .blocks()
                .flat_map(|block| split.block(block).operations())
                .filter(|operation| operation.kind == OperationKind::Move)
                .count();
            assert_eq!(moves, 1, "the whole move must stay one move");
        }
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
        // A call's scalar argument is read where it is evaluated, and its result is stored.
        assert!(
            split.blocks().any(|block| {
                split.block(block).operations().iter().any(|op| {
                    matches!(op.kind, OperationKind::Load | OperationKind::Store)
                        && op.operands.iter().any(
                            |value| matches!(value, Value::Register(id) if fields.contains(id)),
                        )
                })
            }),
            "retained call must read or write a split field directly"
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
