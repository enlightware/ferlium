// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! The shadow-stack discipline of emitted bodies.
//!
//! Emitted bodies allocate on a shadow stack that grows upward in linear memory, and each restores
//! its entry frontier when it returns. A yielded accessor that suspends is the exception: its
//! continuation frame stays on the stack, and its caller may allocate above that frame before
//! resuming it. The caller's storage is therefore not reclaimed in LIFO order across a projection.
//!
//! Stack markers are nevertheless restored without runtime checks, because MIR scopes projections
//! and markers lexically. [`check_nesting`] verifies that, per body:
//!
//! - no projection opened after a marker was saved is still open when the marker is restored, so a
//!   restore never reclaims a suspended continuation;
//! - no marker saved while a projection was open is restored after that projection ended, so a
//!   restore never raises the frontier back into a reclaimed continuation;
//! - no marker saved before a yield is restored after it, so a resumed accessor never reclaims
//!   storage that its caller allocated while it was suspended.
//!
//! Completing a projection reclaims its continuation only if nothing was allocated above it since
//! it suspended. Otherwise the continuation remains until its caller restores an older marker or
//! returns.

use crate::{
    FxHashMap, FxHashSet,
    mir::{Function, Operation, OperationKind, Value, ValueId, terminator::TerminatorKind},
    module::id::Id,
};

use super::control_flow::distinct_targets;

/// What a restore of a marker must not cross.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Opening {
    /// A projection opened after the marker, whose continuation frame may remain above its
    /// caller's frontier.
    Projection(ValueId),
    /// The suspension of this accessor, above which its caller may have allocated.
    Suspension,
    /// A projection that was open when the marker was saved.
    Inside(ValueId),
    /// A projection that was open when the marker was saved and has ended since, possibly
    /// reclaiming the continuation below the marker.
    Ended,
}

#[derive(Clone, Default)]
struct State {
    /// For each saved marker, what may have been opened or ended since it was saved.
    markers: FxHashMap<ValueId, FxHashSet<Opening>>,
    /// The projections that may be open.
    projections: FxHashSet<ValueId>,
}

/// Checks that restoring any stack marker of `body` reclaims only storage allocated since it was
/// saved.
pub(super) fn check_nesting(body: &Function) -> Result<(), String> {
    let mut restores = false;
    let mut openings = false;
    for block in body.blocks() {
        let block = body.block(block);
        for operation in block.operations() {
            restores |= matches!(operation.kind, OperationKind::StackRestore);
            openings |= matches!(operation.kind, OperationKind::Project { .. });
        }
        openings |= match &block.terminator().kind {
            TerminatorKind::Yield { .. } => true,
            TerminatorKind::Invoke { operation, .. } => {
                matches!(operation.kind, OperationKind::Project { .. })
            }
            _ => false,
        };
    }
    if !restores || !openings {
        return Ok(());
    }

    let mut states: Vec<Option<State>> = vec![None; body.blocks().count()];
    states[body.entry().as_index()] = Some(State::default());
    let mut pending = vec![body.entry()];
    while let Some(block) = pending.pop() {
        let mut state = states[block.as_index()]
            .clone()
            .expect("pending blocks are reached");
        let block = body.block(block);
        for operation in block.operations() {
            transfer(&mut state, operation)?;
        }
        let successors = match &block.terminator().kind {
            TerminatorKind::Invoke {
                operation,
                normal,
                error,
            } => {
                let before = state.clone();
                transfer(&mut state, operation)?;
                // A projection that fails to open leaves no continuation behind.
                let failed = if matches!(operation.kind, OperationKind::Project { .. }) {
                    before
                } else {
                    state.clone()
                };
                vec![(*normal, state), (*error, failed)]
            }
            TerminatorKind::Yield { resume, .. } => {
                open(&mut state, Opening::Suspension);
                vec![(*resume, state)]
            }
            kind => distinct_targets(kind)
                .into_iter()
                .map(|target| (target, state.clone()))
                .collect(),
        };
        for (target, state) in successors {
            if merge(&mut states[target.as_index()], state) {
                pending.push(target);
            }
        }
    }
    Ok(())
}

fn transfer(state: &mut State, operation: &Operation) -> Result<(), String> {
    match operation.kind {
        OperationKind::StackSave => {
            if let Some(marker) = operation.result_id() {
                let inside = state.projections.iter().copied().map(Opening::Inside);
                state.markers.insert(marker, inside.collect());
            }
        }
        OperationKind::StackRestore => {
            if let Some(Value::Register(marker)) = operation.operands.first()
                && let Some(opened) = state.markers.get(marker)
            {
                if opened.contains(&Opening::Suspension) {
                    return Err("stack restore across a yield".into());
                }
                if opened.contains(&Opening::Ended) {
                    return Err("stack restore after its enclosing projection ended".into());
                }
                if opened
                    .iter()
                    .any(|opening| matches!(opening, Opening::Projection(_)))
                {
                    return Err("stack restore across an open projection".into());
                }
            }
        }
        OperationKind::Project { .. } => {
            if let Some(projection) = operation.result_id() {
                open(state, Opening::Projection(projection));
                state.projections.insert(projection);
            }
        }
        OperationKind::EndProject => {
            if let Some(Value::Register(projection)) = operation.operands.first() {
                for opened in state.markers.values_mut() {
                    opened.remove(&Opening::Projection(*projection));
                    if opened.remove(&Opening::Inside(*projection)) {
                        opened.insert(Opening::Ended);
                    }
                }
                state.projections.remove(projection);
            }
        }
        _ => (),
    }
    Ok(())
}

fn open(state: &mut State, opening: Opening) {
    for opened in state.markers.values_mut() {
        opened.insert(opening);
    }
}

/// Joins `state` into what reaches a block, returning whether that grew.
fn merge(reached: &mut Option<State>, state: State) -> bool {
    let Some(reached) = reached else {
        *reached = Some(state);
        return true;
    };
    let mut grew = false;
    for projection in state.projections {
        grew |= reached.projections.insert(projection);
    }
    for (marker, opened) in state.markers {
        let reached = reached.markers.entry(marker).or_insert_with(|| {
            grew = true;
            FxHashSet::default()
        });
        for opening in opened {
            grew |= reached.insert(opening);
        }
    }
    grew
}

#[cfg(test)]
mod tests {
    use wasm_bindgen_test::wasm_bindgen_test;

    use super::*;
    use crate::{
        Location,
        mir::{BasicBlock, BlockId, ParameterId, terminator::Terminator, value::ConstantId},
        types::{
            effects::no_effects,
            r#type::{CallImplType, CallResultConvention, FnType, Type},
        },
    };

    fn span() -> Location {
        Location::new_synthesized()
    }

    fn b(index: usize) -> BlockId {
        BlockId::from_index(index)
    }

    fn register(index: usize) -> Value {
        Value::Register(ValueId::from_index(index))
    }

    fn with_result(mut operation: Operation, result: usize) -> Operation {
        operation.assign_result_id(Some(ValueId::from_index(result)));
        operation
    }

    /// Marker register 0.
    fn save() -> Operation {
        with_result(Operation::stack_save(span()), 0)
    }

    fn restore() -> Operation {
        Operation::stack_restore(span(), register(0))
    }

    /// Projection register 1.
    fn project() -> Operation {
        with_result(
            Operation::project(
                span(),
                Value::Parameter(ParameterId::from_index(0)),
                [],
                Type::unit(),
                CallImplType::value(FnType::new_by_val([], Type::unit(), no_effects())),
            ),
            1,
        )
    }

    fn end_project() -> Operation {
        Operation::end_project(span(), register(1))
    }

    fn check(blocks: Vec<(Vec<Operation>, Terminator)>) -> Result<(), String> {
        check_nesting(&Function::new(
            "stack".into(),
            CallResultConvention::Value,
            Vec::new(),
            Vec::new(),
            blocks
                .into_iter()
                .map(|(operations, terminator)| BasicBlock::new(operations, terminator))
                .collect(),
        ))
    }

    #[wasm_bindgen_test]
    fn accepts_projections_closed_before_each_restore() {
        let repeat = Terminator::cond_br(
            span(),
            Value::Constant(ConstantId::from_index(0)),
            b(1),
            b(2),
        );
        assert_eq!(
            check(vec![
                (vec![save()], Terminator::goto(span(), b(1))),
                (vec![project(), end_project(), restore()], repeat),
                (Vec::new(), Terminator::ret(span())),
            ]),
            Ok(())
        );
        // A marker saved while a projection is open is above its continuation.
        assert_eq!(
            check(vec![(
                vec![project(), save(), restore(), end_project()],
                Terminator::ret(span())
            )]),
            Ok(())
        );
    }

    #[wasm_bindgen_test]
    fn rejects_a_restore_across_an_open_projection() {
        assert_eq!(
            check(vec![(
                vec![save(), project(), restore(), end_project()],
                Terminator::ret(span())
            )]),
            Err("stack restore across an open projection".into())
        );
    }

    #[wasm_bindgen_test]
    fn rejects_a_restore_after_its_enclosing_projection_ended() {
        let error = Err("stack restore after its enclosing projection ended".into());
        assert_eq!(
            check(vec![(
                vec![project(), save(), end_project(), restore()],
                Terminator::ret(span())
            )]),
            error
        );
        // A marker saved before the projection on one path and inside it on another.
        let choose = Terminator::cond_br(
            span(),
            Value::Constant(ConstantId::from_index(0)),
            b(1),
            b(2),
        );
        assert_eq!(
            check(vec![
                (Vec::new(), choose),
                (vec![save(), project()], Terminator::goto(span(), b(3))),
                (vec![project(), save()], Terminator::goto(span(), b(3))),
                (vec![end_project(), restore()], Terminator::ret(span())),
            ]),
            error
        );
    }

    #[wasm_bindgen_test]
    fn a_projection_that_fails_to_open_leaves_nothing_open() {
        let blocks = |opened| {
            vec![
                (
                    vec![save()],
                    Terminator::invoke(span(), project(), b(1), b(2)),
                ),
                (opened, Terminator::ret(span())),
                (vec![restore()], Terminator::ret(span())),
            ]
        };
        assert_eq!(check(blocks(vec![end_project(), restore()])), Ok(()));
        assert_eq!(
            check(blocks(vec![restore(), end_project()])),
            Err("stack restore across an open projection".into())
        );
    }

    #[wasm_bindgen_test]
    fn rejects_a_restore_across_a_yield() {
        assert_eq!(
            check(vec![
                (vec![save()], Terminator::r#yield(span(), register(0), b(1))),
                (vec![restore()], Terminator::ret(span())),
            ]),
            Err("stack restore across a yield".into())
        );
    }
}
