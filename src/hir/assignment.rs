// Copyright 2026 Enlightware GmbH
// Licensed under the Apache License, Version 2.0.

//! Expand source assignments after inference resolves accessor argument passing.
//! Captures precede the RHS; destination access scopes contain only the final update.

use super::{self as hir, Node, NodeArena, NodeId, NodeKind, PendingAssignment};
use crate::{
    containers::{SVec2, b},
    hir::function::ArgConvention,
    module::{LocalDecl, LocalDeclId, PendingLocalClone, PendingLocalDrop, id::Id},
    types::{
        effects::no_effects,
        mutability::MutType,
        r#type::{FnArgType, Type},
    },
};
use ustr::ustr;

/// Recursively expand pending assignments into ordinary HIR after argument passing is resolved.
pub(crate) fn lower_pending_assignments(
    arena: &mut NodeArena,
    root: NodeId,
    locals: &mut Vec<LocalDecl>,
) {
    for child in arena[root].kind.child_node_ids() {
        lower_pending_assignments(arena, child, locals);
    }
    let NodeKind::PendingAssignment(plan) = &arena[root].kind else {
        return;
    };
    let plan = plan.clone();
    #[cfg(debug_assertions)]
    let expected_captures = captured_inputs(arena, &plan, &mut |ty| ty)
        .into_iter()
        .filter(|id| {
            capture_needs_storage(&arena[*id], arena[*id].ty, |id| {
                locals[id.as_index()].mut_ty
            })
        })
        .collect();
    let mut lowering = AssignmentLowering {
        arena,
        locals,
        prefix: Vec::new(),
        cleanup: Vec::new(),
        #[cfg(debug_assertions)]
        expected_captures,
    };
    let tail = match *plan {
        PendingAssignment::Update {
            destination,
            rhs,
            update,
            cleanup,
        } => {
            let destination = lowering.prepare(destination);
            lowering.cleanup.extend(cleanup);
            if let Some((binding, body)) = update {
                let NodeKind::Block(setup) = &lowering.arena[rhs].kind else {
                    unreachable!("live assignment RHS setup is a sequence");
                };
                lowering.prefix.extend_from_slice(&setup.body);
                Some(lowering.open(destination, binding, body))
            } else if lowering.arena[destination].ty == Type::never() {
                Some(destination)
            } else {
                Some(rhs)
            }
        }
        PendingAssignment::DivergingInputs {
            callee,
            arguments,
            argument_types,
        } => {
            if let Some(callee) = callee {
                lowering.capture(callee);
            }
            for (index, (argument, ty)) in arguments.into_iter().zip(argument_types).enumerate() {
                if argument_is_place(index, ArgConvention::Let, ty.mut_ty) {
                    lowering.prepare(argument);
                } else {
                    lowering.capture(argument);
                }
            }
            None
        }
    };
    if let Some(tail) = tail {
        lowering.prefix.push(tail);
    }
    if let Some(index) = lowering
        .prefix
        .iter()
        .position(|id| lowering.arena[*id].ty == Type::never())
    {
        lowering.prefix.truncate(index + 1);
    }
    // A pending node is expanded in place, preserving source IDs used by diagnostics and yields.
    lowering.arena[root].kind = if lowering.prefix.len() == 1 && lowering.cleanup.is_empty() {
        lowering.arena[lowering.prefix[0]].kind.clone()
    } else {
        NodeKind::Block(b(hir::Block {
            body: b(SVec2::from_vec(lowering.prefix)),
            cleanup: lowering.cleanup,
        }))
    };
}

/// Builds one assignment's destination captures, deferred access, and cleanup scopes.
struct AssignmentLowering<'a> {
    arena: &'a mut NodeArena,
    locals: &'a mut Vec<LocalDecl>,
    prefix: Vec<NodeId>,
    cleanup: Vec<LocalDeclId>,
    #[cfg(debug_assertions)]
    expected_captures: crate::FxHashSet<NodeId>,
}

fn argument_is_place(index: usize, passing: ArgConvention, mut_ty: MutType) -> bool {
    index == 0 || passing == ArgConvention::MutableRef || mut_ty.is_mutable()
}

/// Shared by evidence activation and lowering: literals and immutable locals already retain
/// their values, while a diverging input never reaches its materialization.
pub(crate) fn capture_needs_storage(
    node: &Node,
    resolved_ty: Type,
    local_mut_ty: impl FnOnce(LocalDeclId) -> MutType,
) -> bool {
    resolved_ty != Type::never()
        && !matches!(node.kind, NodeKind::Immediate(_))
        && !matches!(node.kind, NodeKind::LoadLocal(load)
            if local_mut_ty(load.id) == MutType::constant())
}

impl AssignmentLowering<'_> {
    fn rebuild(&mut self, original: NodeId, kind: NodeKind) -> NodeId {
        let mut node = self.arena[original].clone();
        node.kind = kind;
        self.arena.alloc(node)
    }

    fn prepare(&mut self, place: NodeId) -> NodeId {
        let kind = match self.arena[place].kind.clone() {
            NodeKind::LoadLocal(_) => return place,
            NodeKind::Project(mut node) => {
                node.value = self.prepare(node.value);
                NodeKind::Project(node)
            }
            NodeKind::FieldAccess(mut node) => {
                node.value = self.prepare(node.value);
                NodeKind::FieldAccess(node)
            }
            NodeKind::WithPlace(mut node) => {
                node.place = self.prepare(node.place);
                node.body = self.prepare(node.body);
                node.access = hir::PlaceAccess::Exclusive;
                NodeKind::WithPlace(node)
            }
            NodeKind::WithYielded(mut node) => {
                node.accessor = self.prepare(node.accessor);
                node.body = self.prepare(node.body);
                node.access = hir::PlaceAccess::Exclusive;
                NodeKind::WithYielded(node)
            }
            NodeKind::StaticApply(mut node) if node.ty.result_convention.returns_borrow() => {
                self.arguments(&mut node.arguments, &node.ty.fn_ty.args);
                NodeKind::StaticApply(node)
            }
            NodeKind::TraitMethodApply(mut node) if node.ty.result_convention.returns_borrow() => {
                self.arguments(&mut node.arguments, &node.ty.fn_ty.args);
                NodeKind::TraitMethodApply(node)
            }
            NodeKind::FunctionApply(mut node) if node.ty.result_convention.returns_borrow() => {
                node.function = self.capture(node.function);
                self.arguments(&mut node.arguments, &node.ty.fn_ty.args);
                NodeKind::FunctionApply(node)
            }
            NodeKind::SubscriptApply(mut node) if node.ty.result_convention.returns_borrow() => {
                node.subscript = self.capture(node.subscript);
                self.arguments(&mut node.arguments, &node.ty.fn_ty.args);
                NodeKind::SubscriptApply(node)
            }
            NodeKind::Block(block) if is_place_recipe(self.arena, place) => {
                let (tail, setup) = block.body.split_last().expect("place block has a tail");
                self.prefix.extend_from_slice(setup);
                self.cleanup.extend(block.cleanup);
                return self.prepare(*tail);
            }
            _ => return self.capture(place),
        };
        self.rebuild(place, kind)
    }

    fn arguments(&mut self, arguments: &mut [hir::CallArgument], types: &[FnArgType]) {
        for (index, (argument, ty)) in arguments.iter_mut().zip(types).enumerate() {
            // Inference may have recorded Let while mutability was unresolved. The resolved
            // signature now requires a mutable place; preserve any earlier explicit ABI override.
            if ty.mut_ty.is_mutable() {
                argument.passing = ArgConvention::MutableRef;
            }
            argument.value = if argument_is_place(index, argument.passing, ty.mut_ty) {
                self.prepare(argument.value)
            } else {
                self.capture(argument.value)
            };
        }
    }

    fn capture(&mut self, value: NodeId) -> NodeId {
        if self.arena[value].ty == Type::never() {
            self.prefix.push(value);
            return value;
        }
        if !capture_needs_storage(&self.arena[value], self.arena[value].ty, |id| {
            self.locals[id.as_index()].mut_ty
        }) {
            return value;
        }
        // Check the parallel evidence walk at the materialization site, before rebuilding nodes.
        #[cfg(debug_assertions)]
        debug_assert!(
            self.expected_captures.contains(&value),
            "assignment capture missing from evidence planning: {value:?}"
        );
        let value = self.materialize(value);
        let node = self.arena[value].clone();
        let mut local = LocalDecl::new(
            (ustr("$destination"), crate::Location::new_synthesized()),
            MutType::constant(),
            node.ty,
            None,
            node.span,
        );
        local.set_owned_storage(PendingLocalDrop::Unknown);
        let id = LocalDecl::push_with_next_slot(self.locals, local);
        self.cleanup.push(id);
        self.prefix.push(self.arena.alloc(Node::new(
            NodeKind::StoreLocal(hir::StoreLocal { value, id }),
            Type::unit(),
            node.effects,
            node.span,
        )));
        self.arena.alloc(Node::new(
            NodeKind::LoadLocal(hir::LoadLocal { id }),
            node.ty,
            no_effects(),
            node.span,
        ))
    }

    fn materialize(&mut self, value: NodeId) -> NodeId {
        let kind = match self.arena[value].kind.clone() {
            NodeKind::WithYielded(mut node) => {
                node.body = self.materialize(node.body);
                NodeKind::WithYielded(node)
            }
            NodeKind::WithPlace(mut node) => {
                node.body = self.materialize(node.body);
                NodeKind::WithPlace(node)
            }
            NodeKind::Block(mut block) => {
                if let Some(tail) = block.body.last_mut() {
                    *tail = self.materialize(*tail);
                }
                NodeKind::Block(block)
            }
            _ if hir::node_is_place_reference(self.arena, value) => {
                NodeKind::CloneValue(hir::CloneValue {
                    source: value,
                    clone: PendingLocalClone::Unknown,
                })
            }
            _ => return value,
        };
        self.rebuild(value, kind)
    }

    fn open(&mut self, destination: NodeId, binding: LocalDeclId, body: NodeId) -> NodeId {
        let kind = match self.arena[destination].kind.clone() {
            NodeKind::WithPlace(mut node) => {
                node.body = self.open(node.body, binding, body);
                NodeKind::WithPlace(node)
            }
            NodeKind::WithYielded(mut node) => {
                node.body = self.open(node.body, binding, body);
                NodeKind::WithYielded(node)
            }
            _ => {
                // Inference builds the update against a placeholder binding. Substitute the
                // prepared place at its single opening, without adding another runtime scope.
                match self.arena[body].kind.clone() {
                    NodeKind::Assign(mut assignment)
                        if matches!(self.arena[assignment.place].kind,
                        NodeKind::LoadLocal(load) if load.id == binding) =>
                    {
                        assignment.place = destination;
                        NodeKind::Assign(assignment)
                    }
                    NodeKind::WithPlace(mut node)
                        if matches!(self.arena[node.place].kind,
                        NodeKind::LoadLocal(load) if load.id == binding) =>
                    {
                        node.place = destination;
                        NodeKind::WithPlace(node)
                    }
                    _ => unreachable!("assignment update must use its destination binding once"),
                }
            }
        };
        let effects = kind
            .child_node_ids()
            .iter()
            .flat_map(|id| self.arena[*id].effects.iter())
            .collect();
        self.arena.alloc(Node::new(
            kind,
            self.arena[body].ty,
            effects,
            self.arena[destination].span,
        ))
    }
}

fn is_place_recipe(arena: &NodeArena, node: NodeId) -> bool {
    match &arena[node].kind {
        NodeKind::WithYielded(_) => true,
        NodeKind::StaticApply(call) => call.ty.result_convention.returns_borrow(),
        NodeKind::TraitMethodApply(call) => call.ty.result_convention.returns_borrow(),
        NodeKind::FunctionApply(call) => call.ty.result_convention.returns_borrow(),
        NodeKind::SubscriptApply(call) => call.ty.result_convention.returns_borrow(),
        NodeKind::Block(block) => block
            .tail_node()
            .is_some_and(|tail| is_place_recipe(arena, tail)),
        _ => hir::node_is_place_reference(arena, node),
    }
}

/// Inputs which will need retained values, using the current inference substitution. This is
/// also used before generalization so late materialization has the required `Value` evidence.
pub(crate) fn captured_inputs(
    arena: &NodeArena,
    plan: &PendingAssignment,
    resolve_mut: &mut impl FnMut(MutType) -> MutType,
) -> Vec<NodeId> {
    fn walk(
        arena: &NodeArena,
        node: NodeId,
        resolve: &mut impl FnMut(MutType) -> MutType,
        out: &mut Vec<NodeId>,
    ) {
        let arguments = match &arena[node].kind {
            NodeKind::LoadLocal(_) => return,
            NodeKind::Project(p) => return walk(arena, p.value, resolve, out),
            NodeKind::FieldAccess(p) => return walk(arena, p.value, resolve, out),
            NodeKind::WithPlace(p) => {
                walk(arena, p.place, resolve, out);
                return walk(arena, p.body, resolve, out);
            }
            NodeKind::WithYielded(p) => {
                walk(arena, p.accessor, resolve, out);
                return walk(arena, p.body, resolve, out);
            }
            NodeKind::Block(block) if is_place_recipe(arena, node) => {
                return walk(arena, block.tail_node().unwrap(), resolve, out);
            }
            NodeKind::StaticApply(app) if app.ty.result_convention.returns_borrow() => {
                (&app.arguments, &app.ty.fn_ty.args)
            }
            NodeKind::TraitMethodApply(app) if app.ty.result_convention.returns_borrow() => {
                (&app.arguments, &app.ty.fn_ty.args)
            }
            NodeKind::FunctionApply(app) if app.ty.result_convention.returns_borrow() => {
                out.push(app.function);
                (&app.arguments, &app.ty.fn_ty.args)
            }
            NodeKind::SubscriptApply(app) if app.ty.result_convention.returns_borrow() => {
                out.push(app.subscript);
                (&app.arguments, &app.ty.fn_ty.args)
            }
            _ => {
                out.push(node);
                return;
            }
        };
        for (index, (argument, ty)) in arguments.0.iter().zip(arguments.1).enumerate() {
            if argument_is_place(index, argument.passing, resolve(ty.mut_ty)) {
                walk(arena, argument.value, resolve, out);
            } else {
                out.push(argument.value);
            }
        }
    }
    let mut result = Vec::new();
    match plan {
        PendingAssignment::Update { destination, .. } => {
            walk(arena, *destination, resolve_mut, &mut result)
        }
        PendingAssignment::DivergingInputs {
            callee,
            arguments,
            argument_types,
        } => {
            result.extend(callee);
            for (index, (argument, ty)) in arguments.iter().zip(argument_types).enumerate() {
                if argument_is_place(index, ArgConvention::Let, resolve_mut(ty.mut_ty)) {
                    walk(arena, *argument, resolve_mut, &mut result);
                } else {
                    result.push(*argument);
                }
            }
        }
    }
    result
}
