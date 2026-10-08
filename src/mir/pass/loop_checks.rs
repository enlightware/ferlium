// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Hoisting a range loop's array bounds check into one check before the loop.
//!
//! A check left in a loop because nothing ties the range to the array's length, as in
//! `for j in lo..hi { … a[j] … }`, tests every iteration for what the loop's bounds decide once:
//! the indices `base + stride * j` form one run of consecutive integers, valid exactly when its two
//! ends are. This stage makes that test once, by calling std's `array_loop_indices_check` in the
//! loop's preheader, and turns the in-loop check into a jump. The access keeps its negative-index
//! fixup, because a valid run may hold negative indices.
//!
//! **A failing guard raises the error before the loop runs**, and there is no checked copy of the
//! loop to fall back on. That is sound only because the loop is then certain to fail, and the
//! language lets a loop certain to fail with an index error raise it before running its iterations
//! (see `docs/book`, arrays). Certainty is what the conditions below establish:
//!
//! - the index is `base + stride * cursor`, with `cursor` the value a range iterator yields on entry
//!   to the loop's header and `base` and the length available unchanged before the loop;
//! - every iteration reaches the check: it dominates every back edge, and once the iterator has
//!   advanced, the loop is left only through an error edge, so a `break` or `return` disqualifies
//!   it;
//! - the loop does not write the environment, so raising the error early skips no write the host
//!   could observe. Reads and failures are allowed: a skipped read is unobservable, and an earlier
//!   iteration failing otherwise is a failure the rule lets the index error replace.
//!
//! The guard's own failure needs the cleanup due before the loop. It is the cleanup the in-loop
//! check ran, without what the loop itself set up: stack markers saved in the loop are not restored,
//! and anything else mentioning a value of the loop refuses the hoist.

use std::cell::RefCell;

use rustc_hash::{FxHashMap, FxHashSet};

use super::{
    dataflow::call_operands,
    known_callee::{KnownCallee, KnownCallees},
    loops::{NaturalLoop, cfg, natural_loops},
    relations::{self, Affine, Analysis, DefSite, Holder, Symbol, SymbolId},
    stack_region,
};
use crate::{
    hir::{function::ArgConvention, value::LiteralValue},
    mir::{
        self, BlockId, DebugLocation, Function, Operation, OperationKind, OperationResult,
        ParameterKind,
        dominance::Dominance,
        edit::FunctionEdit,
        terminator::{Terminator, TerminatorKind},
        value::ValueId,
    },
    module::{FunctionId, ModuleEnv, id::Id},
    std::{
        logic::bool_type,
        math::{Int, int_type},
    },
    types::{
        effects::{Effect, PrimitiveEffect},
        r#type::Type,
    },
};

/// A quantity before the loop, as a constant plus a weighted sum of sources.
struct Materialized {
    constant: Int,
    terms: Vec<(Source, Int)>,
}

/// Where a quantity comes from before the loop.
enum Source {
    /// A value that already holds it there.
    Holder(Holder),
    /// A field of a place, its projection computed again before the loop: `operation` with its base
    /// replaced.
    Field(Operation, Box<Source>),
    /// An integer operation the loop computes on quantities it does not change, computed again
    /// before the loop. `y * width` in a loop over `x` is one.
    Computed(KnownCallee, Box<[Materialized; 2]>),
}

/// How deep a quantity's recomputation may go: a product of sums at most.
const MAX_DEPTH: usize = 3;

/// How many projections a place's root may lie below it.
const MAX_PROJECTIONS: usize = 8;

/// Finds where the quantities a guard needs come from before the loop.
struct Sources<'a> {
    func: &'a Function,
    analysis: &'a mut Analysis,
    known: &'a KnownCallees,
    original_of: &'a dyn Fn(FunctionId) -> Option<FunctionId>,
    dominance: &'a Dominance,
    definitions: &'a FxHashMap<ValueId, BlockId>,
    /// Whether an allocation is live after a preheader, shared by the checks of one body: each
    /// answer is a walk of the whole body, and a loop's checks ask about the same allocations.
    liveness: &'a RefCell<FxHashMap<(ValueId, BlockId), bool>>,
    preheader: BlockId,
}

impl Sources<'_> {
    fn materialize(&mut self, form: &Affine, depth: usize) -> Option<Materialized> {
        let terms = form
            .terms()
            .iter()
            .map(|&(symbol, coefficient)| Some((self.source(symbol, depth)?, coefficient)))
            .collect::<Option<Vec<_>>>()?;
        Some(Materialized {
            constant: form.constant,
            terms,
        })
    }

    /// Where `symbol`'s value comes from at the end of the preheader.
    fn source(&mut self, symbol: SymbolId, depth: usize) -> Option<Source> {
        let holders = self.analysis.holders(symbol, self.preheader);
        if let Some(holder) = holders.iter().find(|holder| self.available(holder)) {
            return Some(Source::Holder(holder.clone()));
        }
        if depth >= MAX_DEPTH {
            return None;
        }
        // A place register defined in the loop names the same place before it.
        if let Some(source) = holders.iter().find_map(|holder| match holder {
            Holder::Place(mir::Value::Register(register)) => self.field(*register, depth),
            _ => None,
        }) {
            return Some(source);
        }
        self.computed(symbol, depth)
    }

    /// Whether `register` is defined on every path to the end of the preheader.
    fn defined_before(&self, register: ValueId) -> bool {
        self.definitions.get(&register).is_some_and(|block| {
            self.dominance
                .dominates(block.as_index(), self.preheader.as_index())
        })
    }

    /// Whether `holder` is an `int` the guard can read at the end of the preheader.
    fn available(&self, holder: &Holder) -> bool {
        let defined_before = |register: &ValueId| self.defined_before(*register);
        match holder {
            Holder::Place(mir::Value::Parameter(parameter)) => {
                let parameter = &self.func.parameters()[parameter.as_index()];
                parameter.ty == int_type()
                    && matches!(
                        parameter.kind,
                        ParameterKind::Parameter(ArgConvention::Let) | ParameterKind::Owned
                    )
            }
            Holder::Place(mir::Value::Register(register)) => {
                defined_before(register) && self.int_place(*register) && self.live(*register)
            }
            Holder::Value(register) => {
                defined_before(register)
                    && self.definition(*register).is_some_and(|operation| {
                        operation.result() == OperationResult::Lowered(int_type())
                    })
            }
            Holder::Place(_) => false,
        }
    }

    fn definition(&self, register: ValueId) -> Option<&Operation> {
        let block = *self.definitions.get(&register)?;
        self.func
            .block(block)
            .operations()
            .iter()
            .find(|operation| operation.result_id() == Some(register))
    }

    /// Whether the storage `register` names is still allocated after the preheader. The analysis
    /// tracks values, not lifetimes: a local holding the right value may have been popped by a
    /// restore since.
    fn live(&self, register: ValueId) -> bool {
        let mut place = register;
        for _ in 0..MAX_PROJECTIONS {
            let Some(operation) = self.definition(place) else {
                return false;
            };
            match (&operation.kind, operation.operands.first()) {
                (OperationKind::Alloca { .. }, _) => {
                    return *self
                        .liveness
                        .borrow_mut()
                        .entry((place, self.preheader))
                        .or_insert_with(|| {
                            stack_region::alloca_live_after(self.func, place, self.preheader)
                        });
                }
                (OperationKind::Subfield { .. }, Some(mir::Value::Parameter(_))) => return true,
                (OperationKind::Subfield { .. }, Some(mir::Value::Register(base))) => place = *base,
                _ => return false,
            }
        }
        false
    }

    /// Whether `register` names an `int` place: a local or a product field of that type.
    fn int_place(&self, register: ValueId) -> bool {
        self.definition(register)
            .is_some_and(|operation| match &operation.kind {
                OperationKind::Alloca { ty } => *ty == int_type(),
                OperationKind::Subfield {
                    ty,
                    variant_payload: false,
                    ..
                } => *ty == int_type(),
                _ => false,
            })
    }

    /// The place `register` projects, from a base available before the loop.
    fn field(&mut self, register: ValueId, depth: usize) -> Option<Source> {
        let operation = self.definition(register)?.clone();
        let OperationKind::Subfield {
            variant_payload: false,
            has_layout_witness: false,
            ..
        } = operation.kind
        else {
            return None;
        };
        let [base, mir::Value::Constant(_)] = &*operation.operands else {
            return None;
        };
        let base = match base {
            // Any parameter whose place this projects: its field is what the symbol named.
            mir::Value::Parameter(_) => Source::Holder(Holder::Place(base.clone())),
            mir::Value::Register(base) => {
                if self.defined_before(*base) && self.live(*base) {
                    Source::Holder(Holder::Place(mir::Value::Register(*base)))
                } else if depth + 1 < MAX_DEPTH {
                    self.field(*base, depth + 1)?
                } else {
                    return None;
                }
            }
            _ => return None,
        };
        Some(Source::Field(operation, Box::new(base)))
    }

    /// `symbol` as the integer operation that defined it, on operands available before the loop.
    fn computed(&mut self, symbol: SymbolId, depth: usize) -> Option<Source> {
        let Symbol::Stored(_, DefSite::Operation(site)) = *self.analysis.symbols().name(symbol)
        else {
            return None;
        };
        let operation = self
            .func
            .block(site.block)
            .operations()
            .get(site.index.as_index())?;
        let known = relations::resolved_callee(operation, self.known, self.original_of)?;
        if !matches!(
            known,
            KnownCallee::IntAdd | KnownCallee::IntSub | KnownCallee::IntMul
        ) {
            return None;
        }
        let OperationKind::Call { ty, .. } = &operation.kind else {
            return None;
        };
        let call = call_operands(&operation.operands, ty)?;
        let [(left, _), (right, _)] = call.arguments.as_slice() else {
            return None;
        };
        let (left, right) = ((*left).clone(), (*right).clone());
        let mut forms = None;
        self.analysis.replay(
            self.func,
            self.known,
            self.original_of,
            site.block,
            |_, def, state, interner, _| {
                if def == DefSite::Operation(site) {
                    forms = state
                        .argument_affine(&left, interner)
                        .zip(state.argument_affine(&right, interner));
                }
            },
        );
        let (left, right) = forms?;
        let left = self.materialize(&left, depth + 1)?;
        let right = self.materialize(&right, depth + 1)?;
        Some(Source::Computed(known, Box::new([left, right])))
    }
}

/// One check to hoist, as planned against the unmodified body.
pub(crate) struct Guard {
    /// The block whose branch performs the check, which becomes a jump to `pass`.
    check: BlockId,
    pass: BlockId,
    preheader: BlockId,
    header: BlockId,
    span: DebugLocation,
    base: Materialized,
    stride: Int,
    start: Materialized,
    end: Materialized,
    inclusive: bool,
    length: Materialized,
    /// The in-loop check's cleanup, without what the loop set up.
    cleanup: Vec<Operation>,
    cleanup_terminator: Terminator,
}

/// Plans the guards for the checks left in `func`'s range loops, skipping the checks in `settled`,
/// which the relational proof already removes.
pub(crate) fn plan(
    func: &Function,
    analysis: &mut Analysis,
    known: &KnownCallees,
    original_of: &dyn Fn(FunctionId) -> Option<FunctionId>,
    settled: &FxHashSet<BlockId>,
) -> Vec<Guard> {
    // Most bodies have no range loop, or no access left to fail in one; they pay for no graph.
    if !analysis.has_iterations() {
        return Vec::new();
    }
    let failures: Vec<BlockId> = func
        .blocks()
        .filter(|block| {
            matches!(&func.block(*block).terminator().kind,
                TerminatorKind::Invoke { operation, .. }
                    if relations::resolved_callee(operation, known, original_of)
                        == Some(KnownCallee::ArrayIndexOutOfBounds))
        })
        .collect();
    if failures.is_empty() {
        return Vec::new();
    }
    let (successors, predecessors) = cfg(func);
    let dominance = Dominance::of(&successors, func.entry().as_index());
    let mut loops = natural_loops(func, &successors, &predecessors, &dominance);
    if loops.is_empty() {
        return Vec::new();
    }
    // Innermost first, so that the first loop holding a check is the one it repeats in.
    loops.sort_by_key(|natural| natural.blocks.len());
    let definitions = definition_blocks(func);
    let liveness = RefCell::default();

    let mut guards = Vec::new();
    for failure in failures {
        let TerminatorKind::Invoke { error, .. } = &func.block(failure).terminator().kind else {
            unreachable!("a failure ends with its invoked report");
        };
        let [check] = predecessors[failure.as_index()].as_slice() else {
            continue;
        };
        let check = *check;
        if settled.contains(&check) {
            continue;
        }
        let TerminatorKind::CondBr {
            then_target,
            else_target,
            ..
        } = func.block(check).terminator().kind
        else {
            continue;
        };
        let pass = match (then_target == failure, else_target == failure) {
            (true, false) => else_target,
            (false, true) => then_target,
            _ => continue,
        };
        let Some(natural) = loops.iter().find(|natural| natural.blocks.contains(&check)) else {
            continue;
        };
        let Some((index, length)) = failure_forms(func, analysis, known, original_of, failure)
        else {
            continue;
        };
        if let Some(guard) = plan_one(
            func,
            analysis,
            known,
            original_of,
            &dominance,
            &predecessors,
            &definitions,
            &liveness,
            natural,
            Site {
                check,
                pass,
                failure,
                error: *error,
            },
            index,
            length,
        ) {
            guards.push(guard);
        }
    }
    guards
}

/// The blocks of one check.
struct Site {
    check: BlockId,
    pass: BlockId,
    failure: BlockId,
    error: BlockId,
}

#[allow(clippy::too_many_arguments)]
fn plan_one(
    func: &Function,
    analysis: &mut Analysis,
    known: &KnownCallees,
    original_of: &dyn Fn(FunctionId) -> Option<FunctionId>,
    dominance: &Dominance,
    predecessors: &[Vec<BlockId>],
    definitions: &FxHashMap<ValueId, BlockId>,
    liveness: &RefCell<FxHashMap<(ValueId, BlockId), bool>>,
    natural: &NaturalLoop,
    site: Site,
    index: Affine,
    length: Affine,
) -> Option<Guard> {
    let header = natural.header;
    let preheader = natural.preheader;

    // The index is the cursor, at most once, over a base.
    let mut cursor = None;
    let mut base_terms = Vec::new();
    for &(symbol, coefficient) in index.terms() {
        match analysis.header_cursor(symbol) {
            Some((_, at)) if at == header => {
                if cursor.is_some() || coefficient != 1 {
                    return None;
                }
                cursor = Some(symbol);
            }
            _ => base_terms.push((symbol, coefficient)),
        }
    }
    let cursor = cursor?;
    let (iteration, _) = analysis.header_cursor(cursor)?;
    let inclusive = iteration.inclusive;
    let advances = iteration.advances.clone();
    // The iterator this loop drives: built before the loop, advanced only in it.
    if natural.blocks.contains(&iteration.construction)
        || !advances.iter().all(|block| natural.blocks.contains(block))
    {
        return None;
    }

    // Every iteration reaches the check.
    let latches = predecessors[header.as_index()]
        .iter()
        .filter(|block| natural.blocks.contains(block));
    for latch in latches {
        if !dominance.dominates(site.check.as_index(), latch.as_index()) {
            return None;
        }
    }
    let body = body_region(func, natural, &advances);
    if !body.contains(&site.check) || !leaves_only_by_errors(func, natural, &body) {
        return None;
    }
    if writes_environment(func, natural) {
        return None;
    }

    // The quantities before the loop.
    let mut sources = Sources {
        func,
        analysis,
        known,
        original_of,
        dominance,
        definitions,
        liveness,
        preheader,
    };
    let base_form = base_terms.iter().try_fold(
        Affine::constant(index.constant),
        |sum, &(symbol, coefficient)| sum.add(&Affine::symbol(symbol).scale(coefficient)),
    )?;
    let base = sources.materialize(&base_form, 0)?;
    let length = sources.materialize(&length, 0)?;
    let [start, end] = sources.analysis.range_bounds(cursor, preheader)?;
    let start = sources.materialize(&start, 0)?;
    let end = sources.materialize(&end, 0)?;

    let (cleanup, cleanup_terminator) = cleanup_before(func, natural, definitions, site.error)?;
    Some(Guard {
        check: site.check,
        pass: site.pass,
        preheader,
        header,
        span: func.block(site.failure).terminator().span,
        base,
        stride: 1,
        start,
        end,
        inclusive,
        length,
        cleanup,
        cleanup_terminator,
    })
}

/// The index and length a failing access reports, as forms.
fn failure_forms(
    func: &Function,
    analysis: &mut Analysis,
    known: &KnownCallees,
    original_of: &dyn Fn(FunctionId) -> Option<FunctionId>,
    failure: BlockId,
) -> Option<(Affine, Affine)> {
    let mut forms = None;
    let terminator_index = func.block(failure).operations().len();
    analysis.replay(
        func,
        known,
        original_of,
        failure,
        |operation, def, state, interner, _| {
            if def.operation_index().map(|index| index.as_index()) != Some(terminator_index) {
                return;
            }
            let OperationKind::Call { ty, .. } = &operation.kind else {
                return;
            };
            let Some(call) = call_operands(&operation.operands, ty) else {
                return;
            };
            let [(index, _), (length, _)] = call.arguments.as_slice() else {
                return;
            };
            forms = state
                .argument_affine(index, interner)
                .zip(state.argument_affine(length, interner));
        },
    );
    forms
}

/// The block each register is defined in. An invoked result exists only on its normal edge, so it
/// is left out rather than placed in the invoking block.
fn definition_blocks(func: &Function) -> FxHashMap<ValueId, BlockId> {
    let mut definitions = FxHashMap::default();
    for block in func.blocks() {
        for operation in func.block(block).operations() {
            if let Some(result) = operation.result_id() {
                definitions.insert(result, block);
            }
        }
    }
    definitions
}

/// The loop's blocks that run after its iterator advanced: reachable from an advance without
/// passing the header again.
fn body_region(func: &Function, natural: &NaturalLoop, advances: &[BlockId]) -> FxHashSet<BlockId> {
    let mut body = FxHashSet::default();
    let mut pending: Vec<BlockId> = advances.to_vec();
    while let Some(block) = pending.pop() {
        if block == natural.header || !natural.blocks.contains(&block) || !body.insert(block) {
            continue;
        }
        pending.extend(func.block(block).terminator().successors());
    }
    body
}

/// Whether the body region is left only through error edges: no `break` and no `return`.
fn leaves_only_by_errors(
    func: &Function,
    natural: &NaturalLoop,
    body: &FxHashSet<BlockId>,
) -> bool {
    body.iter().all(|&block| {
        let terminator = &func.block(block).terminator().kind;
        let error = match terminator {
            TerminatorKind::Goto { .. }
            | TerminatorKind::CondBr { .. }
            | TerminatorKind::SwitchVariant { .. } => None,
            TerminatorKind::Invoke { error, .. } => Some(*error),
            _ => return false,
        };
        terminator
            .successors()
            .all(|successor| natural.blocks.contains(&successor) || Some(successor) == error)
    })
}

/// Whether anything in the loop may write the environment, or has effects not yet known.
fn writes_environment(func: &Function, natural: &NaturalLoop) -> bool {
    let projections: FxHashSet<ValueId> = natural
        .blocks
        .iter()
        .flat_map(|block| func.block(*block).operations())
        .filter(|operation| matches!(operation.kind, OperationKind::Project { .. }))
        .filter_map(Operation::result_id)
        .collect();
    natural.blocks.iter().any(|&block| {
        let terminator = match &func.block(block).terminator().kind {
            TerminatorKind::Invoke { operation, .. } => Some(operation),
            _ => None,
        };
        func.block(block)
            .operations()
            .iter()
            .chain(terminator)
            .any(|operation| match &operation.kind {
                OperationKind::Call { ty, .. } | OperationKind::Project { ty, .. } => {
                    let effects = ty.effects();
                    effects.has_variables()
                        || effects.contains(Effect::Primitive(PrimitiveEffect::Write))
                }
                // A slide's effects are its projection's, which must then be one checked above.
                OperationKind::EndProject => !matches!(
                    operation.operands.first(),
                    Some(mir::Value::Register(projection)) if projections.contains(projection)
                ),
                _ => false,
            })
    })
}

/// The cleanup an error raised just before the loop owes, from the cleanup `error` begins for an
/// error raised inside it: the same, without restoring the markers the loop saved.
fn cleanup_before(
    func: &Function,
    natural: &NaturalLoop,
    definitions: &FxHashMap<ValueId, BlockId>,
    error: BlockId,
) -> Option<(Vec<Operation>, Terminator)> {
    let in_loop = |value: &mir::Value| {
        matches!(value, mir::Value::Register(register)
            if definitions.get(register).is_some_and(|block| natural.blocks.contains(block)))
    };
    let mut cleanup = Vec::new();
    for operation in func.block(error).operations() {
        if matches!(operation.kind, OperationKind::StackRestore)
            && operation.operands.iter().all(in_loop)
        {
            continue;
        }
        // A copied result would define its register twice.
        if operation.operands.iter().any(in_loop) || operation.result_id().is_some() {
            return None;
        }
        cleanup.push(operation.clone());
    }
    let terminator = func.block(error).terminator().clone();
    match terminator.kind {
        TerminatorKind::PropagateError => {}
        TerminatorKind::Goto { target } => {
            // The rest of the cleanup is shared with errors raised outside the loop only if it
            // mentions nothing of the loop.
            let mut seen = FxHashSet::default();
            let mut pending = vec![target];
            while let Some(block) = pending.pop() {
                if natural.blocks.contains(&block) {
                    return None;
                }
                if !seen.insert(block) {
                    continue;
                }
                let body = func.block(block);
                if body
                    .operations()
                    .iter()
                    .flat_map(|operation| operation.operands.iter())
                    .chain(body.terminator().operands())
                    .any(in_loop)
                {
                    return None;
                }
                pending.extend(body.terminator().successors());
            }
        }
        _ => return None,
    }
    Some((cleanup, terminator))
}

/// Inserts the planned guards and turns their checks into jumps. Several guards of one loop run
/// one after the other in its preheader, so the first to fail may not guard the access that would
/// have failed first; the language rule lets its error be reported instead.
pub(crate) fn apply(
    edit: &mut FunctionEdit,
    guards: Vec<Guard>,
    known: &KnownCallees,
    env: ModuleEnv<'_>,
) {
    let mut tails: FxHashMap<BlockId, BlockId> = FxHashMap::default();
    for guard in guards {
        let span = guard.span;
        edit.block_mut(guard.check).terminator = Terminator::goto(span, guard.pass);
        let tail = *tails.entry(guard.preheader).or_insert(guard.preheader);
        let mut emitter = Emitter {
            edit: &mut *edit,
            known,
            env,
            block: tail,
            span,
        };
        let base = emitter.quantity(&guard.base);
        let stride = emitter.constant(guard.stride);
        let start = emitter.quantity(&guard.start);
        let end = emitter.quantity(&guard.end);
        let inclusive = emitter.boolean(guard.inclusive);
        let length = emitter.quantity(&guard.length);
        let result = emitter.place(Type::unit());
        let (callee, ty) = known.array_loop_indices_check();
        let call = Operation::call(
            span,
            mir::Value::Function(callee),
            [base, stride, start, end, inclusive, length, result],
            ty.clone(),
        );
        let next = edit.add_block(Terminator::goto(span, guard.header));
        let cleanup = edit.add_block(guard.cleanup_terminator);
        edit.block_mut(cleanup).operations = guard.cleanup;
        edit.block_mut(tail).terminator = Terminator::invoke(span, call, next, cleanup);
        tails.insert(guard.preheader, next);
    }
}

/// Appends the operations computing a guard's arguments to one block.
struct Emitter<'a, 'e> {
    edit: &'a mut FunctionEdit,
    known: &'a KnownCallees,
    env: ModuleEnv<'e>,
    block: BlockId,
    span: DebugLocation,
}

impl Emitter<'_, '_> {
    fn place(&mut self, ty: Type) -> mir::Value {
        self.edit
            .append_operation(self.block, Operation::alloca(self.span, ty))
            .expect("an alloca has a result")
    }

    fn store(&mut self, ty: Type, value: LiteralValue) -> mir::Value {
        let place = self.place(ty);
        let constant = self.edit.add_constant(ty, value, &self.env);
        self.edit.append_operation(
            self.block,
            Operation::store(self.span, mir::Value::Constant(constant), place.clone()),
        );
        place
    }

    fn constant(&mut self, value: Int) -> mir::Value {
        self.store(int_type(), LiteralValue::new_native(value))
    }

    fn boolean(&mut self, value: bool) -> mir::Value {
        self.store(bool_type(), LiteralValue::new_native(value))
    }

    /// A place holding `source`'s quantity.
    fn source(&mut self, source: &Source) -> mir::Value {
        match source {
            Source::Holder(Holder::Place(place)) => place.clone(),
            Source::Holder(Holder::Value(register)) => {
                let place = self.place(int_type());
                self.edit.append_operation(
                    self.block,
                    Operation::store(self.span, mir::Value::Register(*register), place.clone()),
                );
                place
            }
            Source::Field(operation, base) => {
                let base = self.source(base);
                let (kind, operands) = operation.kind_and_operands();
                let mut operands: Box<[mir::Value]> = operands.into();
                operands[0] = base;
                let projection = Operation::from_parts(self.span, operands, kind.clone());
                self.edit
                    .append_operation(self.block, projection)
                    .expect("a projection has a result")
            }
            Source::Computed(known, operands) => {
                let [left, right] = &**operands;
                let left = self.quantity(left);
                let right = self.quantity(right);
                let (callee, ty) = match known {
                    KnownCallee::IntAdd => self.known.int_add(),
                    KnownCallee::IntSub => self.known.int_sub(),
                    _ => self.known.int_mul(),
                };
                let result = self.place(int_type());
                self.edit.append_operation(
                    self.block,
                    Operation::call(
                        self.span,
                        mir::Value::Function(callee),
                        [left, right, result.clone()],
                        ty.clone(),
                    ),
                );
                result
            }
        }
    }

    /// A place holding `quantity`, reusing a source's place when the quantity is exactly it.
    fn quantity(&mut self, quantity: &Materialized) -> mir::Value {
        if let [(source, 1)] = quantity.terms.as_slice()
            && quantity.constant == 0
        {
            return self.source(source);
        }
        let sum = self.constant(quantity.constant);
        for (source, coefficient) in &quantity.terms {
            let mut term = self.source(source);
            if *coefficient != 1 {
                let factor = self.constant(*coefficient);
                let product = self.place(int_type());
                let (callee, ty) = self.known.int_mul();
                self.edit.append_operation(
                    self.block,
                    Operation::call(
                        self.span,
                        mir::Value::Function(callee),
                        [term, factor, product.clone()],
                        ty.clone(),
                    ),
                );
                term = product;
            }
            let (callee, ty) = self.known.int_add();
            self.edit.append_operation(
                self.block,
                Operation::call(
                    self.span,
                    mir::Value::Function(callee),
                    [sum.clone(), term, sum.clone()],
                    ty.clone(),
                ),
            );
        }
        sum
    }
}

#[cfg(test)]
mod tests {
    use crate::{CompilerSession, MirOptimization};

    fn optimized(src: &str) -> String {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        session.emit_mir("loops", src)
    }

    /// The optimized body of `name`, up to the next function.
    fn body_of(module: &str, name: &str) -> String {
        let body = module
            .split(&format!("fn {name}("))
            .nth(1)
            .unwrap_or_else(|| panic!("module has no `{name}`:\n{module}"));
        body.split("\nfn ").next().unwrap().to_string()
    }

    /// How many guards `body` calls and how many in-loop checks it still fails through.
    fn shape(src: &str, name: &str) -> (usize, usize, String) {
        let body = body_of(&optimized(src), name);
        (
            body.matches("array_loop_indices_check(").count(),
            body.matches("array_index_out_of_bounds(").count(),
            body,
        )
    }

    /// The point of the stage: a loop over a range nothing ties to the array checks its indices
    /// once, before it runs, and no longer on each iteration.
    #[test]
    fn a_range_loop_checks_its_indices_before_it_runs() {
        for range in ["lo..hi", "lo..=hi"] {
            let (guards, checks, body) = shape(
                &format!(
                    "fn total(a: [int], lo: int, hi: int) -> int {{ let mut t = 0; for i in {range} {{ t = t + a[i] }}; t }}"
                ),
                "total",
            );
            assert_eq!((guards, checks), (1, 0), "{range}:\n{body}");
        }
    }

    /// A row of a matrix is checked once per row: the index's product is the same on every
    /// iteration of the inner loop, so it is computed again before it.
    #[test]
    fn an_inner_loop_over_a_row_is_checked_once_per_row() {
        let (guards, checks, body) = shape(
            "fn total(a: [int], w: int, h: int) -> int { let mut t = 0; for y in 0..h { for x in 0..w { t = t + a[y * w + x] } }; t }",
            "total",
        );
        assert_eq!((guards, checks), (1, 0), "{body}");
    }

    /// An access some iterations skip is not certain to be reached, so its failure is not certain.
    #[test]
    fn an_access_on_some_iterations_keeps_its_check() {
        for body in [
            "if t < 10 { t = t + a[i] }",
            "if i == 2 { continue }; t = t + a[i]",
        ] {
            let (guards, checks, text) = shape(
                &format!(
                    "fn total(a: [int], lo: int, hi: int) -> int {{ let mut t = 0; for i in lo..hi {{ {body} }}; t }}"
                ),
                "total",
            );
            assert_eq!((guards, checks), (0, 1), "{body}:\n{text}");
        }
    }

    /// A loop that can stop before its failing access may succeed, so it must run to see.
    #[test]
    fn a_loop_that_can_stop_early_keeps_its_check() {
        for body in [
            "if a[i] == 0 { return i }",
            "if t > 10 { break }; t = t + a[i]",
        ] {
            let (guards, checks, text) = shape(
                &format!(
                    "fn total(a: [int], lo: int, hi: int) -> int {{ let mut t = 0; for i in lo..hi {{ {body} }}; t }}"
                ),
                "total",
            );
            assert_eq!((guards, checks), (0, 1), "{body}:\n{text}");
        }
    }

    /// A length the loop changes is not the length before it.
    #[test]
    fn a_loop_growing_its_array_keeps_its_check() {
        let (guards, checks, body) = shape(
            "fn total(mut a: [int], lo: int, hi: int) -> int { let mut t = 0; for i in lo..hi { t = t + a[i]; array_append(a, t) }; t }",
            "total",
        );
        assert_eq!((guards, checks), (0, 1), "{body}");
    }

    /// Raising the error early skips the loop's environment writes, which the host would see; its
    /// reads it would not.
    #[test]
    fn only_a_loop_writing_the_environment_keeps_its_check() {
        for (effect, guarded) in [("write", false), ("read", true)] {
            let (guards, checks, body) = shape(
                &format!(
                    "fn total(a: [int], lo: int, hi: int, f: (int) -> int ! {effect}) -> int {{ let mut t = 0; for i in lo..hi {{ t = t + f(a[i]) }}; t }}"
                ),
                "total",
            );
            let expected = if guarded { (1, 0) } else { (0, 1) };
            assert_eq!((guards, checks), expected, "{effect}:\n{body}");
        }
    }
}
