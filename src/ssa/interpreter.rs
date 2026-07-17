//! A reference interpreter for the SSA form of Ferlium.
//!
//! The interpreter exists to check that `emit_ssa` lowers HIR to *semantically correct* SSA: it
//! runs a lowered [`ssa::Function`] and produces the value the function computes. It reuses the HIR
//! interpreter's memory substrate — an SSA *place* (pointer) is a [`Place`] and the heap is
//! the [`EvalCtx`]'s `environment`. Native (std) callees are delegated to the HIR interpreter; SSA
//! (script) callees are interpreted recursively so their own lowering is exercised too.

use std::collections::VecDeque;
use std::rc::Rc;

use rustc_hash::FxHashMap;

use crate::{
    CompilerSession, Location,
    emit_ssa::build_ssa_function,
    eval::{
        ControlFlow, EvalCtx, Place, PlaceResult, RuntimeError, ValOrMut,
        call_value_clone_for_temp, call_value_drop_for_temp,
    },
    execution::ReferenceInterpreterLimits,
    hir::{
        function::{ArgConvention, copy_boxed_trivial_copy_native},
        value::{FunctionValue, HiddenEvidenceArgValue, LiteralValue, SubscriptValue, Value},
    },
    module::{
        FunctionId, LocalFunctionId, ModuleEnv, ModuleId, TraitDictionaryId, id::Id,
        trait_impl::TraitDictionaryEntry,
    },
    ssa::{self, BlockId, InstructionId, InstructionKind},
    std::buffer,
    types::{
        r#trait::TraitDictionaryEntryIndex,
        r#type::{Type, TypeKind},
    },
};

/// A key uniquely identifying a function across modules.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct FunctionKey {
    pub module: ModuleId,
    pub identity: LocalFunctionId,
}

/// The runtime binding of an SSA register or parameter: either a materialized value (the result of
/// a `load`/`comp_eq`) or a place (the result of an `alloca`/`project`, or an incoming by-pointer
/// parameter).
///
/// A non-trivially-copyable value is *moved* out of its binding by its single consuming use. The
/// interpreter leaves a boxed-HIR `Value::Uninit` tombstone in this private binding map so a second
/// read panics loudly (see `value_operand`). Absence is not representable as an `ssa::Value` operand;
/// this is dynamic validation of SSA single-consumption, not part of the IR value model.
enum Binding {
    Value(Value),
    Place(Place),
    /// A symbolic trait dictionary (an interned id), the binding of a `Dictionary` constant or a
    /// forwarded dictionary `@extra` parameter. Dispatched through `DictArg::Interned`; never
    /// materialized into a tuple.
    Dictionary(TraitDictionaryId),
    /// A saved top of the stack (the `environment` length), the result of a `stack_save`.
    StackMarker(usize),
    /// An open scoped projection (the result of a `project`): the exposed yielded place — used by the
    /// body exactly like a `Place` binding — together with the suspended accessor frame that
    /// `end_project` resumes. Removed from the register map by its `end_project`.
    Projected {
        place: Place,
        frame: Box<SuspendedFrame>,
    },
}

/// The control-flow effect of executing a single instruction.
enum Step {
    /// Continue with the next instruction in the block.
    Advance,
    /// Transfer control to the start of the given block.
    Goto(BlockId),
    /// Return from the current function (the result is already in the return out-pointer).
    Return,
    /// Resume the unwind that this frame's cleanup pad interrupted: hand the in-flight error back to
    /// the caller so propagation continues up the stack.
    ///
    /// When a language failure or execution cancellation reaches a cleanup edge, the error does not
    /// leave the frame immediately: control first enters a pad that runs the frame's drops. That pad
    /// has *paused* the unwind. After the drops, this step (the pad's `resume` terminator) lets it
    /// continue: the same error — stashed when control entered the pad — is returned to the caller,
    /// whose explicit or implicit call-site edge can run its own pad. The error is *continued*, not
    /// newly raised, which is why it is `resume` and not a throw.
    Resume,
    /// Suspend the current frame at a `yield`, exposing the carried place to the driving `project`.
    /// The frame's registers and stack cells stay live; `end_project` later resumes it (mirrors the
    /// HIR interpreter's `ControlTransfer::Yield`).
    Suspend(Place),
}

/// The outcome of running a frame's instruction loop ([`Interpreter::run_loop`]): it either ran to a
/// `ret`/`resume` (`Completed`) or hit a `yield` (`Suspended`), in which case the live register map
/// and the resume point are handed back so a later `end_project` can continue the accessor's slide.
enum FrameOutcome {
    Completed,
    Suspended {
        /// The yielded place (`yield`'s operand), exposed as the `project`'s result.
        place: Place,
        /// The block holding the instructions after the `yield`.
        block: BlockId,
        /// The index of the first post-`yield` instruction within `block`.
        idx: usize,
        /// The accessor frame's live register/parameter bindings.
        slots: FxHashMap<ssa::Value, Binding>,
    },
}

/// Which side of a call the storage-state contract (`doc/ssa-ir.md` §4.3) is being checked on.
#[cfg(debug_assertions)]
#[derive(Clone, Copy)]
enum CallPhase {
    Before,
    After,
}

#[cfg(debug_assertions)]
impl std::fmt::Display for CallPhase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            CallPhase::Before => "before",
            CallPhase::After => "after",
        })
    }
}

/// A suspended `YieldedOnce` accessor frame, kept alive between a `project` and its `end_project`
/// (the SSA analog of the HIR interpreter's `SuspendedAccessor`).
struct SuspendedFrame {
    /// The accessor function.
    key: FunctionKey,
    /// The block to resume into (the one containing the `yield`).
    block: BlockId,
    /// The index of the first post-`yield` instruction within `block`.
    idx: usize,
    /// The accessor frame's live register/parameter bindings.
    slots: FxHashMap<ssa::Value, Binding>,
    /// The `environment` length captured at the `project`, so `end_project` reclaims the accessor's
    /// stack cells once its slide completes (mirrors `truncate_environment_storage`).
    frame_top: usize,
}

/// The state of an SSA interpreter.
pub struct Interpreter<'a> {
    /// The HIR evaluation context; its `environment` doubles as the SSA heap.
    ctx: EvalCtx<'a>,
    /// The compiler session, used to resolve and lazily lower callees.
    session: &'a CompilerSession,
    /// Lazily built and cached SSA bodies of called functions.
    cache: FxHashMap<FunctionKey, Rc<ssa::Function>>,
}

impl<'a> Interpreter<'a> {
    /// Creates an interpreter whose initial module context is `module_id`.
    pub fn new(module_id: ModuleId, session: &'a CompilerSession) -> Self {
        Self::with_limits(module_id, session, ReferenceInterpreterLimits::default())
    }

    /// Creates an interpreter with backend-independent execution limits.
    pub fn with_limits(
        module_id: ModuleId,
        session: &'a CompilerSession,
        limits: ReferenceInterpreterLimits,
    ) -> Self {
        Self {
            ctx: EvalCtx::with_limits(module_id, session, limits),
            session,
            cache: FxHashMap::default(),
        }
    }

    /// Whether a failure during semantic unwind made this interpreter unsafe to re-enter.
    pub fn is_poisoned(&self) -> bool {
        self.ctx.is_poisoned()
    }

    /// Runs the no-argument entry function `main_id` of `module_id`.
    pub fn run_main(
        &mut self,
        module_id: ModuleId,
        main_id: LocalFunctionId,
    ) -> Result<Value, RuntimeError> {
        self.run_entry(module_id, main_id, vec![])
    }

    /// Runs an entry function with caller-owned by-value arguments and returns its result value, or
    /// the [`RuntimeError`] it raised.
    ///
    /// Entry functions cannot require hidden dictionary parameters. An ordinary error has already
    /// unwound the callee's frames through their cleanup pads; a hard abort has instead reclaimed
    /// all known interpreter-owned roots without running further Ferlium cleanup.
    pub fn run_entry(
        &mut self,
        module_id: ModuleId,
        entry_id: LocalFunctionId,
        arguments: Vec<Value>,
    ) -> Result<Value, RuntimeError> {
        if let Err(error) = self.ctx.ensure_runnable() {
            for argument in arguments {
                argument.discard_storage();
            }
            return Err(error);
        }
        let key = FunctionKey {
            module: module_id,
            identity: entry_id,
        };
        let func = self.function(key);
        let parameter_tags = func
            .parameters()
            .iter()
            .map(|parameter| parameter.tag)
            .collect::<Vec<_>>();
        assert_eq!(
            parameter_tags.len(),
            arguments.len() + 1,
            "SSA entry arguments must match its visible parameters"
        );
        assert!(
            parameter_tags[..arguments.len()]
                .iter()
                .all(|tag| matches!(tag, ssa::ParameterTag::Parameter(_))),
            "SSA entry functions cannot require hidden dictionary parameters"
        );
        assert_eq!(parameter_tags.last(), Some(&ssa::ParameterTag::Return));

        let entry_top = self.ctx.environment.len();
        let required_cells = arguments.len() + 1;
        if entry_top.saturating_add(required_cells) > self.ctx.environment_cell_limit {
            for argument in arguments {
                argument.discard_storage();
            }
            return Err(self.ctx.environment_cell_limit_error(None));
        }

        let span = Location::new_synthesized();
        let mut bindings = Vec::with_capacity(required_cells);
        for argument in arguments {
            let place = self
                .alloc_cell(argument, span)
                .expect("entry argument capacity was checked above");
            bindings.push(Binding::Place(place));
        }

        // The final parameter is the caller-allocated return out-pointer; shape it from the return
        // type so the callee can `project`/`store` its result fields into it.
        let ret_ty = self
            .session
            .expect_fresh_module(module_id)
            .get_function_by_id(entry_id)
            .unwrap()
            .definition
            .ty_scheme
            .ty
            .ret;
        let init = self.shaped_uninitialized_value(ret_ty);
        let ret = self
            .alloc_cell(init, span)
            .expect("entry return capacity was checked above");
        bindings.push(Binding::Place(ret.clone()));

        #[cfg(debug_assertions)]
        let boundary = Self::call_boundary(&parameter_tags, &bindings);
        #[cfg(debug_assertions)]
        self.check_call_boundary(&boundary, CallPhase::Before);
        if let Err(error) = self.run_function(key, bindings) {
            self.reclaim_frame_storage(entry_top);
            return Err(error);
        }
        #[cfg(debug_assertions)]
        self.check_call_boundary(&boundary, CallPhase::After);
        let slot = ret
            .target_mut(&mut self.ctx)
            .expect("return cell must be addressable");
        let value = std::mem::replace(slot, Value::uninit());
        self.reclaim_frame_storage(entry_top);
        Ok(value)
    }

    /// Returns the lowered SSA body of `key`, building and caching it on first use.
    fn function(&mut self, key: FunctionKey) -> Rc<ssa::Function> {
        if let Some(f) = self.cache.get(&key) {
            return f.clone();
        }
        let module = self.session.expect_fresh_module(key.module);
        let others = self.session.raw_modules();
        let f = Rc::new(build_ssa_function(
            key.identity,
            module,
            others,
            self.session,
        ));
        self.cache.insert(key, f.clone());
        f
    }

    /// Runs `key`'s body with the given parameter bindings (in slot order). The function writes its
    /// result through the return out-pointer parameter, so this returns no value. Final HIR places
    /// `CheckCallDepth` in recursive functions; lowering preserves that check explicitly, so frame
    /// entry only maintains the counter and does not impose an additional backend-specific limit.
    fn run_function(&mut self, key: FunctionKey, args: Vec<Binding>) -> Result<(), RuntimeError> {
        // Parameters point into caller-owned storage. Everything allocated above this marker belongs
        // to the callee and must be reclaimed when its frame completes or unwinds. Addressor-place
        // results are statically required to remain caller-rooted, while yielded accessors use the
        // separate suspended-frame path and restore their saved marker in `exec_end_project`.
        let frame_top = self.ctx.environment.len();
        self.ctx.call_depth += 1;
        let result = self.run_frame(key, args);
        self.ctx.call_depth -= 1;
        self.reclaim_frame_storage(frame_top);
        result
    }

    /// Runs one already-depth-checked call frame (see [`run_function`](Self::run_function)). A plain
    /// call frame must run to completion: suspending out of it (a `YieldedOnce` accessor reached
    /// other than through a `project`) is a lowering bug.
    fn run_frame(&mut self, key: FunctionKey, args: Vec<Binding>) -> Result<(), RuntimeError> {
        let func = self.function(key);
        let mut slots: FxHashMap<ssa::Value, Binding> = FxHashMap::default();
        for (i, b) in args.into_iter().enumerate() {
            slots.insert(ssa::Value::Parameter(ssa::ParameterId::from_index(i)), b);
        }
        match self.run_loop(&func, slots, func.entry(), 0)? {
            FrameOutcome::Completed => Ok(()),
            FrameOutcome::Suspended { .. } => {
                panic!(
                    "a frame suspended outside a `project` driver (YieldedOnce called as a plain function)"
                )
            }
        }
    }

    /// Runs `func`'s instruction stream starting at `(block, idx)` with the given live `slots`, until
    /// it either completes (`ret`/`resume`) or suspends at a `yield`. Used both for a fresh frame
    /// (from its entry) and to resume a suspended accessor's slide (from after its `yield`).
    fn run_loop(
        &mut self,
        func: &ssa::Function,
        mut slots: FxHashMap<ssa::Value, Binding>,
        mut block: BlockId,
        mut idx: usize,
    ) -> Result<FrameOutcome, RuntimeError> {
        let mut instructions: Vec<InstructionId> = func.block(block).instructions().collect();
        // The error in flight through this frame's cleanup pads: set when an `invoke` diverts control
        // to its unwind pad, taken when the chain of pads ends in a `resume` that re-raises it. It is
        // always consumed (at `resume`) before the `Err` leaves this frame, so a nested call's own
        // in-flight error never overlaps with this one.
        let mut pending: Option<RuntimeError> = None;
        loop {
            let i = instructions[idx];
            let step = match self.exec(func, &mut slots, &mut pending, i) {
                Ok(step) => step,
                Err(error) => {
                    if error.is_hard_abort() {
                        self.discard_bindings_after_hard_abort(slots);
                        return Err(error);
                    }
                    if let Some(initial) = pending.take() {
                        let error = self.ctx.poison(initial, error);
                        self.discard_bindings_after_hard_abort(slots);
                        return Err(error);
                    }
                    let Some(unwind) = func.implicit_unwind_target(i) else {
                        self.discard_inactive_bindings(slots);
                        return Err(error);
                    };
                    pending = Some(error);
                    Step::Goto(unwind)
                }
            };
            match step {
                Step::Advance => idx += 1,
                Step::Goto(b) => {
                    block = b;
                    instructions = func.block(block).instructions().collect();
                    idx = 0;
                }
                Step::Return => {
                    self.discard_inactive_bindings(slots);
                    return Ok(FrameOutcome::Completed);
                }
                Step::Resume => {
                    let error = pending
                        .take()
                        .expect("resume reached without an in-flight error");
                    self.discard_inactive_bindings(slots);
                    return Err(error);
                }
                // Suspend at the `yield`: hand back the live frame and the resume point (the
                // instruction right after the `yield`) for a later `end_project`.
                Step::Suspend(place) => {
                    return Ok(FrameOutcome::Suspended {
                        place,
                        block,
                        idx: idx + 1,
                        slots,
                    });
                }
            }
        }
    }

    /// Executes the instruction `i` of `func` within the current frame `slots`.
    fn exec(
        &mut self,
        func: &ssa::Function,
        slots: &mut FxHashMap<ssa::Value, Binding>,
        pending: &mut Option<RuntimeError>,
        i: InstructionId,
    ) -> Result<Step, RuntimeError> {
        let instr = func.at(i);
        let def = func.definition(i);
        let span = instr.span;
        Ok(match &instr.kind {
            InstructionKind::Alloca { ty } => {
                let init = self.shaped_uninitialized_value(*ty);
                let place = self.alloc_cell(init, span)?;
                slots.insert(def.unwrap(), Binding::Place(place));
                Step::Advance
            }
            InstructionKind::AllocaPlace { .. } => {
                let place = self.alloc_cell(Value::uninit(), span)?;
                slots.insert(def.unwrap(), Binding::Place(place));
                Step::Advance
            }
            InstructionKind::Subfield { .. } => {
                self.exec_subfield(func, slots, &instr.operands, def.unwrap());
                Step::Advance
            }
            InstructionKind::DictEntry { entry_index, .. } => {
                self.exec_dict_entry(slots, &instr.operands, def.unwrap(), *entry_index, span)?;
                Step::Advance
            }
            InstructionKind::SubscriptMember { mut_member, .. } => {
                self.exec_subscript_member(
                    slots,
                    &instr.operands,
                    def.unwrap(),
                    *mut_member,
                    span,
                )?;
                Step::Advance
            }
            InstructionKind::BuildSubscript { .. } => {
                self.exec_build_subscript(slots, &instr.operands, def.unwrap());
                Step::Advance
            }
            InstructionKind::Load => {
                self.exec_load(slots, &instr.operands, def.unwrap())?;
                Step::Advance
            }
            InstructionKind::Store => {
                self.exec_store(func, slots, &instr.operands)?;
                Step::Advance
            }
            InstructionKind::Clear => {
                self.exec_clear(slots, &instr.operands[0]);
                Step::Advance
            }
            InstructionKind::Memcpy => {
                self.exec_memcpy(slots, &instr.operands)?;
                Step::Advance
            }
            InstructionKind::Move => {
                self.exec_move(slots, &instr.operands)?;
                Step::Advance
            }
            InstructionKind::CompareEqual => {
                self.exec_compare_equal(func, slots, &instr.operands, def.unwrap());
                Step::Advance
            }
            InstructionKind::ConditionalBranch {
                on_success,
                on_failure,
            } => {
                let c = self.value_operand(func, slots, &instr.operands[0]);
                let taken = *c
                    .as_primitive_ty::<bool>()
                    .expect("condbr condition must be a bool");
                Step::Goto(if taken { *on_success } else { *on_failure })
            }
            InstructionKind::UnconditionalBranch { target } => Step::Goto(*target),
            InstructionKind::Ret => Step::Return,
            InstructionKind::Variant { tag, .. } => {
                // Build a tagged variant shell with an uninitialized payload. The constructing site
                // stores it into the variant's destination and then fills the payload in place
                // through a projection of that destination, so the payload aggregate is never
                // materialized into a temporary. A flat `Uninit` payload grows into the right
                // aggregate skeleton on the first field store (see `grow_value_to_path`); a unit
                // payload is written explicitly by the emitter.
                slots.insert(
                    def.unwrap(),
                    Binding::Value(Value::raw_variant(*tag, Value::uninit())),
                );
                Step::Advance
            }
            InstructionKind::ExtractTag => {
                self.exec_extract_tag(slots, &instr.operands, def.unwrap());
                Step::Advance
            }
            InstructionKind::Call => {
                self.exec_call(slots, &instr.operands, span)?;
                Step::Advance
            }
            InstructionKind::Invoke { normal, unwind } => {
                // A fallible call: on a raised error, stash it and divert to the cleanup pad rather
                // than propagating straight out of the frame. The pad drops this frame's live locals
                // (husk-skipping anything already dropped/moved) and ends in `br <outer pad>` or
                // `resume`, the latter re-raising `pending` to the caller (see the loop in
                // `run_function`). On normal completion control falls through to the continuation.
                match self.exec_call(slots, &instr.operands, span) {
                    Ok(()) => Step::Goto(*normal),
                    Err(err) => {
                        if err.is_hard_abort() {
                            return Err(err);
                        }
                        if let Some(initial) = pending.take() {
                            return Err(self.ctx.poison(initial, err));
                        }
                        *pending = Some(err);
                        Step::Goto(*unwind)
                    }
                }
            }
            InstructionKind::Resume => Step::Resume,
            InstructionKind::Project { ty } => {
                // Enter a scoped subscript: run the accessor to its `yield`, bind the exposed place
                // (and the suspended frame) to this register, and continue with the body.
                self.exec_project(slots, &instr.operands, def.unwrap(), *ty, span)?;
                Step::Advance
            }
            InstructionKind::Yield => {
                // Suspend the accessor, exposing the place at operand `0` to the driving `project`.
                let place = self.place_operand(slots, &instr.operands[0]);
                Step::Suspend(place)
            }
            InstructionKind::EndProject => self.exec_end_project(slots, &instr.operands)?,
            InstructionKind::Drop => {
                self.exec_drop(slots, &instr.operands, span)?;
                Step::Advance
            }
            InstructionKind::StackSave => {
                let marker = self.ctx.environment.len();
                slots.insert(def.unwrap(), Binding::StackMarker(marker));
                Step::Advance
            }
            InstructionKind::StackRestore => {
                let marker = self.stack_marker_operand(slots, &instr.operands[0]);
                self.restore_stack(marker);
                Step::Advance
            }
            InstructionKind::CheckCallDepth { successors } => {
                return self
                    .exec_runtime_check(pending, *successors, |ctx| ctx.check_call_depth(span));
            }
            InstructionKind::CheckFuel { successors } => {
                return self.exec_runtime_check(pending, *successors, |ctx| ctx.check_fuel(span));
            }
            InstructionKind::BuildClosure {
                function,
                num_hidden_dicts,
                has_env_dict,
                ..
            } => {
                let closure = self.exec_build_closure(
                    slots,
                    &instr.operands,
                    function,
                    *num_hidden_dicts as usize,
                    *has_env_dict,
                )?;
                slots.insert(def.unwrap(), Binding::Value(closure));
                Step::Advance
            }
            InstructionKind::CloneClosureEnv { .. } => {
                let cloned = self.exec_clone_closure_env(slots, &instr.operands[0], span)?;
                slots.insert(def.unwrap(), Binding::Value(cloned));
                Step::Advance
            }
            InstructionKind::DropClosureEnv => {
                self.exec_drop_closure_env(slots, &instr.operands[0], span)?;
                Step::Advance
            }
        })
    }

    fn exec_runtime_check(
        &mut self,
        pending: &mut Option<RuntimeError>,
        successors: Option<(BlockId, BlockId)>,
        check: impl FnOnce(&mut EvalCtx<'a>) -> crate::eval::EvalControlFlowResult,
    ) -> Result<Step, RuntimeError> {
        match check(&mut self.ctx) {
            Ok(result) => {
                result.into_value().discard_storage();
                Ok(successors.map_or(Step::Advance, |(normal, _)| Step::Goto(normal)))
            }
            Err(error) => {
                if error.is_hard_abort() {
                    return Err(error);
                }
                if let Some(initial) = pending.take() {
                    return Err(self.ctx.poison(initial, error));
                }
                if let Some((_, unwind)) = successors {
                    *pending = Some(error);
                    Ok(Step::Goto(unwind))
                } else {
                    Err(error)
                }
            }
        }
    }

    /// Executes a `subfield` instruction. The field index is the `int` value at operand `1` — a
    /// constant for a static field, or a register holding a run-time offset. Either way it
    /// resolves to an `isize`.
    #[inline(never)]
    fn exec_subfield(
        &mut self,
        func: &ssa::Function,
        slots: &mut FxHashMap<ssa::Value, Binding>,
        operands: &[ssa::Value],
        def: ssa::Value,
    ) {
        let mut place = self.place_operand(slots, &operands[0]);
        let index = self.value_operand(func, slots, &operands[1]);
        let index = *index
            .as_primitive_ty::<isize>()
            .expect("subfield index must be an int");
        place.path.push(index);
        slots.insert(def, Binding::Place(place));
    }

    /// Executes a `dict_entry` instruction: the symbolic analog of `subfield`. Resolves the
    /// dictionary operand to its interned id, reads function entry `entry_index` straight from the
    /// impl arena, and materializes it into a fresh cell
    /// whose place is bound — so `call`/`drop`/`memcpy` consume it exactly as a `project` result.
    #[inline(never)]
    fn exec_dict_entry(
        &mut self,
        slots: &mut FxHashMap<ssa::Value, Binding>,
        operands: &[ssa::Value],
        def: ssa::Value,
        entry_index: TraitDictionaryEntryIndex,
        span: Location,
    ) -> Result<(), RuntimeError> {
        let id = self.dict_operand(slots, &operands[0]);
        let entry = self.ctx.dictionary_value(id).entry(entry_index);
        let value = match entry {
            TraitDictionaryEntry::Function(function) => Value::function(FunctionId {
                module: id.module_id,
                function,
            }),
        };
        let place = self.alloc_cell(value, span)?;
        slots.insert(def, Binding::Place(place));
        Ok(())
    }

    /// Executes a `subscript_member` instruction: the member-resolving analog of `dict_entry` for
    /// a first-class subscript. Resolves the subscript operand to its runtime value, picks its
    /// `ref`/`mut` member, and materializes the member function value — bundling the subscript's
    /// captured hidden evidence — into a fresh cell, so a `call`/`project` consumes it exactly
    /// like a closure callee (prepending that evidence).
    #[inline(never)]
    fn exec_subscript_member(
        &mut self,
        slots: &mut FxHashMap<ssa::Value, Binding>,
        operands: &[ssa::Value],
        def: ssa::Value,
        mut_member: bool,
        span: Location,
    ) -> Result<(), RuntimeError> {
        let subscript = self.subscript_operand(slots, &operands[0]);
        let function = self
            .ctx
            .subscript_member_function(subscript.subscript, mut_member);
        let value = if subscript.hidden_args.is_empty() {
            Value::function(function)
        } else {
            Value::function_value(FunctionValue::closure(
                function,
                subscript.hidden_args,
                vec![],
                None,
            ))
        };
        let place = self.alloc_cell(value, span)?;
        slots.insert(def, Binding::Place(place));
        Ok(())
    }

    /// Executes a `build_subscript` instruction: bundles the base subscript with captured hidden
    /// evidence, mirroring `eval_build_subscript_value` — each capture operand is interned
    /// evidence, a symbolic dictionary or a subscript value read (non-consumingly) from its
    /// operand.
    #[inline(never)]
    fn exec_build_subscript(
        &mut self,
        slots: &mut FxHashMap<ssa::Value, Binding>,
        operands: &[ssa::Value],
        def: ssa::Value,
    ) {
        let mut subscript = self.subscript_operand(slots, &operands[0]);
        for op in &operands[1..] {
            let arg = match self.try_dict_operand(slots, op) {
                Some(id) => HiddenEvidenceArgValue::TraitDictionary(id),
                None => HiddenEvidenceArgValue::Subscript(crate::containers::b(
                    self.subscript_operand(slots, op),
                )),
            };
            subscript.hidden_args.push(arg);
        }
        slots.insert(def, Binding::Value(Value::subscript_value(subscript)));
    }

    /// Executes a `load` instruction.
    #[inline(never)]
    fn exec_load(
        &mut self,
        slots: &mut FxHashMap<ssa::Value, Binding>,
        operands: &[ssa::Value],
        def: ssa::Value,
    ) -> Result<(), RuntimeError> {
        let place = self.place_operand(slots, &operands[0]);
        let v = self.load_copy(&place);
        slots.insert(def, Binding::Value(v));
        Ok(())
    }

    /// Executes a `store` instruction. The stored operand is normally a value; the one exception
    /// is an `AddressorPlace` return, whose body ends by storing a *place* register — the returned
    /// place pointer (see `doc/ssa-ir.md` §4.2) — into the `@ret` slot. A place-bound operand
    /// therefore stores the bridged `PlaceResult` pointer value, exactly the form a native
    /// addressor returns.
    #[inline(never)]
    fn exec_store(
        &mut self,
        func: &ssa::Function,
        slots: &mut FxHashMap<ssa::Value, Binding>,
        operands: &[ssa::Value],
    ) -> Result<(), RuntimeError> {
        let v = match &operands[0] {
            op @ (ssa::Value::Register(_) | ssa::Value::Parameter(_))
                if matches!(slots.get(op), Some(Binding::Place(_))) =>
            {
                Value::native(PlaceResult::new(self.place_operand(slots, op)))
            }
            op => self.value_operand(func, slots, op),
        };
        let place = self.place_operand(slots, &operands[1]);
        self.store(v, &place)
    }

    /// Marks a place absent without running semantic drop. The overwritten state must already own
    /// no resource; `clear` is the explicit SSA representation of initialization state, not a
    /// replacement for `drop`.
    fn exec_clear(&mut self, slots: &FxHashMap<ssa::Value, Binding>, operand: &ssa::Value) {
        let place = self.place_operand(slots, operand);
        self.materialize_path(&place);
        let slot = place
            .target_mut(&mut self.ctx)
            .expect("clear of an invalid place");
        let husk = husk_like(slot);
        let old = std::mem::replace(slot, husk);
        old.discard_storage();
    }

    /// Executes a `memcpy` instruction as a source-preserving representation copy. The boxed
    /// interpreter copies native opt-in leaves and tuple-backed aggregates recursively; any other
    /// representation is an SSA mis-lowering and fails rather than accidentally becoming a move.
    #[inline(never)]
    fn exec_memcpy(
        &mut self,
        slots: &mut FxHashMap<ssa::Value, Binding>,
        operands: &[ssa::Value],
    ) -> Result<(), RuntimeError> {
        let source = self.place_operand(slots, &operands[0]);
        let destination = self.place_operand(slots, &operands[1]);
        let v = read_copy(
            source
                .target_ref(&self.ctx)
                .expect("memcpy of an invalid source place"),
        )
        .expect(
            "memcpy source is not structurally TrivialCopy: use Value::clone or an ownership move",
        );
        self.store(v, &destination)
    }

    /// Executes a `move` instruction: a source-consuming move. Reads the source place out (leaving
    /// it uninitialized) and writes it straight into the destination place. The optional layout
    /// witness is metadata a backend uses to size the copy; the interpreter moves shape-agnostically
    /// and ignores it.
    #[inline(never)]
    fn exec_move(
        &mut self,
        slots: &mut FxHashMap<ssa::Value, Binding>,
        operands: &[ssa::Value],
    ) -> Result<(), RuntimeError> {
        let source = self.place_operand(slots, &operands[0]);
        let destination = self.place_operand(slots, &operands[1]);
        let v = self.take(&source);
        self.store(v, &destination)
    }

    /// Executes a `comp_eq` instruction: a lowered `match` comparison. The scrutinee is read
    /// non-consumingly and the pattern's immutable literal representation compares directly with
    /// the runtime value. This preserves the HIR invariant that matching an owned value never
    /// converts it back into compiler constant data.
    #[inline(never)]
    fn exec_compare_equal(
        &mut self,
        func: &ssa::Function,
        slots: &mut FxHashMap<ssa::Value, Binding>,
        operands: &[ssa::Value],
        def: ssa::Value,
    ) {
        let pattern = self.pattern_literal_operand(&operands[1]);
        let equal = self.with_runtime_value(func, slots, &operands[0], |scrutinee| {
            pattern
                .try_matches_runtime_value(scrutinee)
                .expect("SSA match pattern and scrutinee have incompatible representations")
        });
        slots.insert(def, Binding::Value(Value::native(equal)));
    }

    /// Executes an `extract_tag` instruction: reads the variant's tag without consuming it (the
    /// payload stays live for the match arms), encoded as the same `int` the HIR interpreter
    /// produces.
    #[inline(never)]
    fn exec_extract_tag(
        &mut self,
        slots: &mut FxHashMap<ssa::Value, Binding>,
        operands: &[ssa::Value],
        def: ssa::Value,
    ) {
        let place = self.place_operand(slots, &operands[0]);
        let value = place
            .target_ref(&self.ctx)
            .expect("extract_tag of an invalid place");
        let variant = value
            .as_variant()
            .expect("extract_tag of a non-variant value");
        let tag = variant.tag_as_isize();
        slots.insert(def, Binding::Value(Value::native(tag)));
    }

    /// Executes an `end_project` instruction: resumes the accessor's slide to completion and
    /// reclaims its frame. Reached on the normal path and inside cleanup pads
    /// (epilogue-on-unwind).
    #[inline(never)]
    fn exec_end_project(
        &mut self,
        slots: &mut FxHashMap<ssa::Value, Binding>,
        operands: &[ssa::Value],
    ) -> Result<Step, RuntimeError> {
        let SuspendedFrame {
            key,
            block,
            idx,
            slots: acc_slots,
            frame_top,
        } = match slots.remove(&operands[0]) {
            Some(Binding::Projected { frame, .. }) => *frame,
            // A projection that completed immediately (an `AddressorPlace` member reached
            // through `project`'s runtime convention dispatch) has no suspended slide:
            // nothing to resume.
            Some(Binding::Place(_)) => return Ok(Step::Advance),
            _ => panic!("end_project operand is not an open projection"),
        };
        let func = self.function(key);
        let result = self.run_loop(&func, acc_slots, block, idx);
        // The accessor frame is torn down whichever way its slide ends: drop the depth it
        // held since the `project` and reclaim its stack cells, then surface any slide error.
        self.ctx.call_depth -= 1;
        self.reclaim_frame_storage(frame_top);
        match result? {
            FrameOutcome::Completed => Ok(Step::Advance),
            FrameOutcome::Suspended { .. } => {
                panic!("a YieldedOnce accessor yielded more than once")
            }
        }
    }

    /// Executes a `drop` instruction `[target, callee]`: if `target`'s pointee is initialized, runs
    /// the `Value::drop` `callee` on it and leaves the cell uninitialized.
    fn exec_drop(
        &mut self,
        slots: &mut FxHashMap<ssa::Value, Binding>,
        operands: &[ssa::Value],
        span: Location,
    ) -> Result<(), RuntimeError> {
        let target = self.place_operand(slots, &operands[0]);
        // Skip the drop if the pointee carries nothing live — either a flat `Uninit` (moved-out /
        // never-initialized) value, or an aggregate skeleton whose every leaf is `Uninit` (left
        // behind by a previous drop of the same storage). This is what makes inline drops run at
        // most once per value.
        let skip = {
            let v = target
                .target_ref_allow_uninit(&self.ctx)
                .expect("drop target must be addressable");
            is_drop_husk(v)
        };
        if skip {
            return Ok(());
        }
        let (module, identity) = self.callee_target(slots, &operands[1]);
        let f = self
            .session
            .expect_fresh_module(module)
            .get_function_by_id(identity)
            .expect("drop callee not found");
        let drop_result = if f.code.as_script().is_some() {
            // A script `Value::drop(&mut self)` in the uniform by-pointer ABI: `drop(self, ())`. Its
            // `()` out-pointer starts a husk like any `@ret`; the drop body writes it (discarded after).
            match self.alloc_cell(Value::uninit(), span) {
                Ok(unit_ret) => self.run_function(
                    FunctionKey { module, identity },
                    vec![Binding::Place(target.clone()), Binding::Place(unit_ret)],
                ),
                Err(error) => Err(error),
            }
        } else {
            // Delegate to the HIR interpreter with the callee's module given explicitly; the
            // delegate rotates its own ambient module internally, so the SSA interpreter never
            // touches `ctx.module_id` (its IR is fully module-resolved).
            self.ctx
                .call_resolved_function_with_extra(
                    FunctionId {
                        module,
                        function: identity,
                    },
                    vec![],
                    vec![ValOrMut::Mut(target.clone())],
                    span,
                )
                .map(|result| match result {
                    ControlFlow::Continue(v) => v.discard_storage(),
                    ControlFlow::Transfer(_) => {
                        panic!("unexpected control transfer from a drop")
                    }
                })
        };

        // Once a semantic-drop action starts, its target lifetime has ended even if the call
        // raises before entering the body: the value may already be partially destroyed and must
        // never be observed or retried. Preserve only the aggregate skeleton so assignment can
        // reinitialize it field by field.
        let slot = target
            .target_mut(&mut self.ctx)
            .expect("drop target must be addressable");
        let husk = std::mem::replace(slot, Value::uninit());
        let skeleton = husk_like(&husk);
        *target
            .target_mut(&mut self.ctx)
            .expect("drop target must be addressable") = skeleton;
        husk.discard_storage();
        drop_result
    }

    /// Executes a `call` instruction whose operands are `[callee, args.., return-out-pointer]`.
    ///
    /// Per the `call` contract (see [`ssa::Instruction::call`]), the callee operand is either a
    /// constant [`ssa::Value::Function`] (a direct static call) or the **place** of a first-class
    /// function value — a function variable, a closure, or a method slot projected out of a
    /// dictionary/witness table. The function value is read *by reference* and never loaded into a
    /// register, so a non-trivially-copyable closure environment is never copied or moved. A bare
    /// function value is called directly; a closure is applied by cloning its captured environment
    /// and prepending the environment slots (see [`exec_closure_call`](Self::exec_closure_call)),
    /// leaving the closure itself in place for its scope-cleanup drop.
    fn exec_call(
        &mut self,
        slots: &mut FxHashMap<ssa::Value, Binding>,
        operands: &[ssa::Value],
        span: Location,
    ) -> Result<(), RuntimeError> {
        let arg_ops = &operands[1..];
        let callee_op = &operands[0];

        // A constant function reference is a direct (bare) call.
        if let ssa::Value::Function(r) = callee_op {
            return self.exec_resolved_call(
                slots,
                r.module,
                r.function,
                Vec::new(),
                0,
                arg_ops,
                span,
            );
        }

        // Otherwise the callee operand is the place of a first-class function value, read by
        // reference (never consumed).
        let place = self.place_operand(slots, callee_op);
        let (module_id, function_id, is_closure) = {
            let fv = place
                .target_ref(&self.ctx)
                .expect("indirect call of an invalid place")
                .as_function()
                .expect("indirect call on a non-function value");
            (
                fv.function.module,
                fv.function.function,
                fv.closure_env_len != 0 || !fv.hidden_args.is_empty(),
            )
        };
        if is_closure {
            self.exec_closure_call(slots, &place, arg_ops, span)
        } else {
            self.exec_resolved_call(slots, module_id, function_id, Vec::new(), 0, arg_ops, span)
        }
    }

    /// Executes a `project` instruction `[callee, args.., ret-out]`: runs the `YieldedOnce` accessor
    /// `callee` to its `yield`, keeping the accessor frame live, and binds `def` to the exposed
    /// yielded place plus the suspended frame (a [`Binding::Projected`]). Mirrors the HIR
    /// interpreter's `call_accessor_until_yield`: the call depth incremented here stays held until the
    /// matching `end_project` resumes the slide and tears the frame down.
    fn exec_project(
        &mut self,
        slots: &mut FxHashMap<ssa::Value, Binding>,
        operands: &[ssa::Value],
        def: ssa::Value,
        _ty: Type,
        span: Location,
    ) -> Result<(), RuntimeError> {
        // A statically known accessor is a direct function reference; a member resolved through
        // subscript evidence (`subscript_member`) is the place of a function value bundling the
        // subscript's captured hidden evidence, which is prepended as the leading `@extra`
        // bindings exactly as `exec_closure_call` prepends a closure's (a subscript member carries
        // no captured environment).
        let (key, leading) = match &operands[0] {
            ssa::Value::Function(r) => (
                FunctionKey {
                    module: r.module,
                    identity: r.function,
                },
                Vec::new(),
            ),
            op => {
                let place = self.place_operand(slots, op);
                let (function, hidden_args) = {
                    let fv = place
                        .target_ref(&self.ctx)
                        .expect("project callee of an invalid place")
                        .as_function()
                        .expect("project callee must be a function value");
                    assert_eq!(
                        fv.closure_env_len, 0,
                        "a projection accessor has no captured environment"
                    );
                    (fv.function, fv.hidden_args.clone())
                };
                let mut leading: Vec<Binding> = Vec::with_capacity(hidden_args.len());
                for arg in &hidden_args {
                    leading.push(match arg {
                        HiddenEvidenceArgValue::TraitDictionary(id) => Binding::Dictionary(*id),
                        HiddenEvidenceArgValue::Subscript(subscript) => {
                            Binding::Place(self.alloc_cell(
                                Value::subscript_value(subscript.as_ref().clone()),
                                span,
                            )?)
                        }
                    });
                }
                (
                    FunctionKey {
                        module: function.module,
                        identity: function.function,
                    },
                    leading,
                )
            }
        };

        // A member reached through subscript evidence is dispatched on its *runtime* shape,
        // mirroring `eval_accessor_until_yield`: the generic caller cannot know whether the
        // concrete member is native or script, or whether it yields or returns a caller-rooted
        // place.
        let f = self
            .session
            .expect_fresh_module(key.module)
            .get_function_by_id(key.identity)
            .expect("project callee not found");
        let convention = f.definition.return_convention();

        if f.code.as_script().is_none() {
            // A native member cannot suspend, so it must return a caller-rooted place: delegate to
            // the HIR interpreter exactly like a native `call` (see `exec_resolved_call`) and bind
            // the returned place. Its `end_project` is then a no-op.
            assert!(
                convention.returns_place(),
                "a native member reached through `project` must return a place"
            );
            assert!(
                leading.is_empty(),
                "a native subscript member takes no captured evidence"
            );
            let passing = f.parameter_passing.clone();
            let n_vis = passing.len();
            let arg_ops = &operands[1..];
            let extra_count = arg_ops
                .len()
                .checked_sub(n_vis)
                .expect("a native member call must pass its visible arguments");
            let (extra_ops, visible_ops) = arg_ops.split_at(extra_count);
            let mut args: Vec<ValOrMut> = Vec::with_capacity(extra_count + n_vis);
            for op in extra_ops {
                let arg = if let Some(id) = self.try_dict_operand(slots, op) {
                    ValOrMut::Dictionary(id)
                } else if let ssa::Value::Subscript(id) = op {
                    ValOrMut::Val(Value::subscript(*id))
                } else {
                    ValOrMut::Mut(self.place_operand(slots, op))
                };
                args.push(arg);
            }
            for (arg_passing, op) in passing.iter().zip(visible_ops) {
                let place = self.place_operand(slots, op);
                match arg_passing {
                    ArgConvention::Let | ArgConvention::MutableRef => {
                        args.push(ValOrMut::Mut(place));
                    }
                }
            }
            let result = self.ctx.call_resolved_function_with_extra(
                FunctionId {
                    module: key.module,
                    function: key.identity,
                },
                vec![],
                args,
                span,
            );
            let value = match result? {
                ControlFlow::Continue(v) => v,
                ControlFlow::Transfer(_) => {
                    panic!("unexpected control transfer from a native call")
                }
            };
            let place = value
                .as_primitive_ty::<PlaceResult>()
                .expect("an addressor member must return a place")
                .place()
                .clone();
            slots.insert(def, Binding::Place(place));
            return Ok(());
        }

        // Marshal the argument operands by the callee's static parameter tags — identical to the
        // script branch of `exec_resolved_call` (an extra parameter binds to its interned dictionary
        // or by-pointer place; every other operand, including the unused return out-pointer, binds to
        // its place).
        let param_tags: Vec<ssa::ParameterTag> = self
            .function(key)
            .parameters()
            .iter()
            .map(|p| p.tag)
            .collect();
        let arg_ops = &operands[1..];
        let offset = leading.len();
        let mut args: Vec<Binding> = Vec::with_capacity(offset + arg_ops.len());
        args.extend(leading);
        for (k, op) in arg_ops.iter().enumerate() {
            let binding = match param_tags.get(offset + k) {
                Some(ssa::ParameterTag::Dictionary) => self.evidence_binding(slots, op, span)?,
                _ => Binding::Place(self.place_operand(slots, op)),
            };
            args.push(binding);
        }

        // An `AddressorPlace` (script) member completes immediately — call it with a synthesized
        // place out-slot and bind the returned place directly; its `end_project` is then a no-op
        // (an addressor has no slide). A `YieldedOnce` member runs to its `yield` below.
        if convention.returns_place() {
            let out = self.alloc_cell(Value::uninit(), span)?;
            args.push(Binding::Place(out.clone()));
            self.run_function(key, args)?;
            let place = self
                .load_copy(&out)
                .as_primitive_ty::<PlaceResult>()
                .expect("an AddressorPlace member must return a place through its out-slot")
                .place()
                .clone();
            slots.insert(def, Binding::Place(place));
            return Ok(());
        }

        // Enter the accessor frame, recording the stack top so `end_project` can later reclaim its
        // cells. A recursive accessor carries the same explicit prologue check as any other
        // recursive function.
        self.ctx.call_depth += 1;
        let frame_top = self.ctx.environment.len();
        let func = self.function(key);
        let mut acc_slots: FxHashMap<ssa::Value, Binding> = FxHashMap::default();
        for (i, b) in args.into_iter().enumerate() {
            acc_slots.insert(ssa::Value::Parameter(ssa::ParameterId::from_index(i)), b);
        }
        match self.run_loop(&func, acc_slots, func.entry(), 0) {
            Ok(FrameOutcome::Suspended {
                place,
                block,
                idx,
                slots: acc_slots,
            }) => {
                // Keep the depth incremented: the accessor frame is still live (resumed at
                // `end_project`).
                slots.insert(
                    def,
                    Binding::Projected {
                        place,
                        frame: Box::new(SuspendedFrame {
                            key,
                            block,
                            idx,
                            slots: acc_slots,
                            frame_top,
                        }),
                    },
                );
                Ok(())
            }
            Ok(FrameOutcome::Completed) => {
                self.ctx.call_depth -= 1;
                panic!("a YieldedOnce accessor returned without yielding")
            }
            Err(err) => {
                self.ctx.call_depth -= 1;
                self.reclaim_frame_storage(frame_top);
                Err(err)
            }
        }
    }

    /// Pairs each by-pointer-bound parameter with the place it was bound to, for the call-boundary
    /// contract check. `Dictionary`-interned bindings (a symbolic trait dictionary, which has no
    /// pointee) are dropped; everything place-bound — visible arguments, the return out-pointer, and
    /// place-carried evidence — is kept with its tag.
    #[cfg(debug_assertions)]
    fn call_boundary(
        tags: &[ssa::ParameterTag],
        args: &[Binding],
    ) -> Vec<(ssa::ParameterTag, Place)> {
        tags.iter()
            .zip(args)
            .filter_map(|(tag, binding)| match binding {
                Binding::Place(place) => Some((*tag, place.clone())),
                _ => None,
            })
            .collect()
    }

    /// Asserts the storage-state contract at a script-call boundary (debug only; `doc/ssa-ir.md`
    /// §4.3): a `&mut`/`&`/trivial-copy argument points at a **live** value both before and after the
    /// call; the return out-pointer is **fresh** (an uninitialized husk, or a unit cell that carries
    /// nothing to drop) before the call and **fully initialized** when the callee returns normally.
    /// Evidence (an interned dictionary) is not value storage and is skipped.
    #[cfg(debug_assertions)]
    fn check_call_boundary(&self, boundary: &[(ssa::ParameterTag, Place)], phase: CallPhase) {
        for (tag, place) in boundary {
            // Read the pointee. A place that projects through (or ends at) uninitialized storage has
            // no value to read — `boundary_pointee` returns `None`, which the check treats as a husk
            // (the slot is simply not initialized).
            let is_husk = self.boundary_pointee(place).is_none_or(is_drop_husk);
            match tag {
                // A `&mut`/`&`/trivial-copy argument must point at a live value, before and after.
                ssa::ParameterTag::Parameter(passing) => assert!(
                    !is_husk,
                    "SSA call boundary: an argument passed as {passing:?} is a husk {phase} the \
                     call; a `&mut`/`&`/trivial-copy argument must point at a live value",
                ),
                // The return out-pointer must be fully initialized when the callee returns normally.
                // There is no dynamic precondition on `@ret` here: the caller-side SSA ownership
                // analysis checks identifiable result storage, and opaque caller-owned storage is a
                // calling-convention contract.
                ssa::ParameterTag::Return => {
                    if matches!(phase, CallPhase::After) {
                        assert!(
                            !is_husk,
                            "SSA call boundary: the return out-pointer must be fully initialized when \
                             the callee returns normally",
                        );
                    }
                }
                ssa::ParameterTag::Dictionary => {}
            }
        }
    }

    /// Reads the value at `place` for the call-boundary check, returning `None` when the place
    /// projects through (or ends at) uninitialized storage — that slot is simply not initialized,
    /// which the contract treats as a husk. Unlike [`Place::target_ref_allow_uninit`], this never
    /// panics on an uninitialized (or otherwise non-navigable) intermediate.
    #[cfg(debug_assertions)]
    fn boundary_pointee(&self, place: &Place) -> Option<&Value> {
        let mut path: VecDeque<isize> = place.path.iter().copied().collect();
        let mut index = place.target;
        let mut target = loop {
            match self.ctx.environment.get(index)? {
                ValOrMut::Val(t) => break t,
                // SAFETY: the referent outlives the borrow, as in `target_ref_allow_uninit`.
                ValOrMut::Ref(t) => break unsafe { &**t },
                ValOrMut::Mut(p) => {
                    index = p.target;
                    for &i in p.path.iter().rev() {
                        path.push_front(i);
                    }
                }
                ValOrMut::Dictionary(_) => return None,
            }
        };
        for &i in &path {
            target = match target {
                Value::Tuple(t) => t.get(i as usize)?,
                Value::Variant(v) if i == 0 => &v.value,
                Value::Native(p) => p
                    .as_ref()
                    .as_any()
                    .downcast_ref::<buffer::Buffer>()?
                    .get_signed(i)?,
                // `Uninit` (or any non-compound) along the path: the slot is not initialized.
                _ => return None,
            };
        }
        Some(target)
    }

    /// Calls the resolved function `(callee_module, callee_identity)` with `leading` (a closure's
    /// prepended `@extra` dictionary evidence and captured-environment slots, in signature order;
    /// empty for a non-closure call) ahead of the visible arguments `arg_ops` (the last of which is
    /// the return out-pointer). `closure_env_len` identifies the trailing value-capture bindings in
    /// `leading`, keeping them distinct from evidence bindings even though both may be places.
    #[allow(clippy::too_many_arguments)]
    fn exec_resolved_call(
        &mut self,
        slots: &mut FxHashMap<ssa::Value, Binding>,
        callee_module: ModuleId,
        callee_identity: LocalFunctionId,
        leading: Vec<Binding>,
        closure_env_len: usize,
        arg_ops: &[ssa::Value],
        span: Location,
    ) -> Result<(), RuntimeError> {
        let key = FunctionKey {
            module: callee_module,
            identity: callee_identity,
        };
        let module = self.session.expect_fresh_module(callee_module);
        let f = module
            .get_function_by_id(callee_identity)
            .expect("callee function not found");
        let is_script = f.code.as_script().is_some();

        if is_script {
            // Uniform by-pointer ABI: the prepended closure evidence/environment bindings come
            // first, then the argument operands straight through (the last is the return
            // out-pointer). Each argument operand is classified by the callee's *static* parameter
            // tag — a `Dictionary` parameter binds to the operand's interned dictionary id, every
            // other parameter binds to its by-pointer place. Classifying by the callee's tag (rather
            // than guessing from the operand's runtime binding) is essential: a value operand must
            // bind as a place even if it could superficially resolve to a dictionary.
            let param_tags: Vec<ssa::ParameterTag> = self
                .function(key)
                .parameters()
                .iter()
                .map(|p| p.tag)
                .collect();
            let offset = leading.len();
            let mut args: Vec<Binding> = Vec::with_capacity(offset + arg_ops.len());
            args.extend(leading);
            for (k, op) in arg_ops.iter().enumerate() {
                let binding = match param_tags.get(offset + k) {
                    // An extra parameter is either a trait dictionary (binds to its interned id) or
                    // subscript evidence (a subscript value passed by place) — both share the
                    // `Dictionary` tag, so the operand disambiguates them. A non-extra
                    // (visible/return) parameter is always a by-pointer place, never reinterpreted
                    // as a dictionary.
                    Some(ssa::ParameterTag::Dictionary) => {
                        self.evidence_binding(slots, op, span)?
                    }
                    _ => Binding::Place(self.place_operand(slots, op)),
                };
                args.push(binding);
            }
            // Check the storage-state contract at the call boundary (debug only; see `doc/ssa-ir.md`
            // §4.3). Only the *visible* operand arguments and the return out-pointer are checked: the
            // leading closure-environment slots (`[..offset]`) are excluded, because the body may
            // legitimately consume a captured value, leaving its (per-call cloned) slot a husk.
            #[cfg(debug_assertions)]
            let boundary = Self::call_boundary(&param_tags[offset..], &args[offset..]);
            #[cfg(debug_assertions)]
            self.check_call_boundary(&boundary, CallPhase::Before);
            self.run_function(key, args)?;
            // Reached only on a *normal* return — an error `?`-propagated above, so the post-condition
            // (which holds only on normal completion) is not checked on the error path.
            #[cfg(debug_assertions)]
            self.check_call_boundary(&boundary, CallPhase::After);
            return Ok(());
        }

        self.exec_resolved_native_call(
            slots,
            callee_module,
            callee_identity,
            leading,
            closure_env_len,
            arg_ops,
            span,
        )
    }

    /// The native branch of [`exec_resolved_call`](Self::exec_resolved_call): marshals the extra
    /// (evidence) arguments and the visible arguments, delegates to the HIR interpreter, then
    /// writes the returned value through the return out-pointer. Kept out of the script call path
    /// so the recursion's per-frame stack stays small.
    #[inline(never)]
    #[allow(clippy::too_many_arguments)]
    fn exec_resolved_native_call(
        &mut self,
        slots: &mut FxHashMap<ssa::Value, Binding>,
        callee_module: ModuleId,
        callee_identity: LocalFunctionId,
        leading: Vec<Binding>,
        closure_env_len: usize,
        arg_ops: &[ssa::Value],
        span: Location,
    ) -> Result<(), RuntimeError> {
        let module = self.session.expect_fresh_module(callee_module);
        let f = module
            .get_function_by_id(callee_identity)
            .expect("callee function not found");

        // Native callee: marshal the extra (dictionary) arguments and the visible arguments,
        // delegate to the HIR interpreter, then write the returned value through the return
        // out-pointer.
        //
        // A call's operands are laid out as `[extra dictionaries…, visible args…, return
        // out-pointer]`. A first-class constrained native instead carries some or all of those
        // extras in `leading`. `parameter_passing` describes only the visible arguments, while the
        // native callable's runtime passing includes hidden evidence followed by visible arguments.
        assert_eq!(
            closure_env_len, 0,
            "a native function closure contains unexpected value captures"
        );
        let passing = f.parameter_passing.clone();
        let n_vis = passing.len();
        let operand_extra_count = arg_ops.len().checked_sub(n_vis + 1).expect(
            "a native call must pass the visible arguments and a return out-pointer at minimum",
        );
        let extra_count = leading.len() + operand_extra_count;
        if let Some(runtime_passing) = f.code.runtime_argument_passing() {
            let expected_extra_count = runtime_passing
                .len()
                .checked_sub(n_vis)
                .expect("native runtime argument passing must include all visible arguments");
            assert_eq!(
                extra_count, expected_extra_count,
                "native call hidden arguments do not match its runtime argument passing"
            );
        }
        let (extra_ops, rest) = arg_ops.split_at(operand_extra_count);
        let (visible_ops, ret_op) = rest.split_at(n_vis);
        let ret_place = self.place_operand(slots, &ret_op[0]);

        let mut args: Vec<ValOrMut> = Vec::with_capacity(extra_count + n_vis);
        // Captured hidden evidence from a first-class constrained native. Trait dictionaries remain
        // interned metadata; subscript evidence is represented by the materialized place allocated
        // by `exec_closure_call`.
        for binding in leading {
            args.push(match binding {
                Binding::Dictionary(id) => ValOrMut::Dictionary(id),
                Binding::Place(place) => ValOrMut::Mut(place),
                Binding::Value(_) | Binding::StackMarker(_) | Binding::Projected { .. } => {
                    panic!("a native function closure contains invalid hidden evidence")
                }
            });
        }
        // Extra arguments: a symbolic trait dictionary is passed as interned evidence
        // (`ValOrMut::Dictionary`), exactly as the HIR interpreter passes a dictionary; subscript
        // evidence is passed as an owned subscript value (mirroring
        // `eval::evidence_arg_to_val_or_mut`), or by reference to its place when forwarded.
        for op in extra_ops {
            let arg = if let Some(id) = self.try_dict_operand(slots, op) {
                ValOrMut::Dictionary(id)
            } else if let ssa::Value::Subscript(id) = op {
                ValOrMut::Val(Value::subscript(*id))
            } else {
                ValOrMut::Mut(self.place_operand(slots, op))
            };
            args.push(arg);
        }
        // Visible arguments, marshaled per the callee's resolved passing.
        for (arg_passing, op) in passing.iter().zip(visible_ops) {
            let place = self.place_operand(slots, op);
            match arg_passing {
                ArgConvention::Let | ArgConvention::MutableRef => {
                    args.push(ValOrMut::Mut(place));
                }
            }
        }

        // Delegate to the HIR interpreter with the callee's module given explicitly; the delegate
        // rotates its own ambient module internally, so the SSA interpreter never touches
        // `ctx.module_id` (its IR is fully module-resolved).
        let result = self.ctx.call_resolved_function_with_extra(
            FunctionId {
                module: callee_module,
                function: callee_identity,
            },
            vec![],
            args,
            span,
        );
        let value = match result? {
            ControlFlow::Continue(v) => v,
            ControlFlow::Transfer(_) => panic!("unexpected control transfer from a native call"),
        };
        self.store(value, &ret_place)?;
        Ok(())
    }

    /// Applies the closure at `place` (borrowed, not consumed), mirroring
    /// [`EvalCtx::call_function_value`]: the captured environment is cloned into a fresh temporary
    /// (so per-call mutations do not persist into the stored closure — closures are stateless across
    /// calls), the environment slots are prepended as leading by-pointer arguments, the body runs,
    /// then the environment temporary is dropped. The closure itself stays in `place` (and is dropped
    /// by its scope cleanup), so it survives repeated calls.
    fn exec_closure_call(
        &mut self,
        slots: &mut FxHashMap<ssa::Value, Binding>,
        place: &Place,
        arg_ops: &[ssa::Value],
        span: Location,
    ) -> Result<(), RuntimeError> {
        let (module_id, function_id, hidden_args, env_len, env_dict, env_ptr) = {
            let fv = place
                .target_ref(&self.ctx)
                .expect("closure call of an invalid place")
                .as_function()
                .expect("closure call on a non-function");
            (
                fv.function.module,
                fv.function.function,
                fv.hidden_args.clone(),
                fv.closure_env_len,
                fv.closure_env_value_dictionary,
                &fv.closure_env as *const Value,
            )
        };

        // The marker captured before allocating any temporary (the materialized subscript-evidence
        // cells and the cloned environment) lets us reclaim them — and the callee's frame storage —
        // afterwards.
        let marker = self.ctx.environment.len();

        // Prepend the closure's hidden `@extra` dictionary evidence, in signature order: a trait
        // dictionary binds to its interned id; subscript evidence is materialized into a cell and
        // passed by place (mirroring `eval::evidence_arg_to_val_or_mut`). These come ahead of the
        // environment slots, matching the lambda signature `[@extra dicts…, captures…, visible…, ret]`.
        let mut leading: Vec<Binding> = Vec::with_capacity(hidden_args.len() + env_len);
        for arg in &hidden_args {
            match arg {
                HiddenEvidenceArgValue::TraitDictionary(id) => {
                    leading.push(Binding::Dictionary(*id));
                }
                HiddenEvidenceArgValue::Subscript(subscript) => {
                    let place =
                        self.alloc_cell(Value::subscript_value(subscript.as_ref().clone()), span)?;
                    leading.push(Binding::Place(place));
                }
            }
        }

        // Clone the captured environment into a fresh environment temporary. `env_ptr` points into
        // the closure's heap box (stable across `environment` growth).
        // Check before cloning so a limit failure cannot leave a freshly cloned managed
        // environment requiring semantic cleanup outside SSA's explicit drop path.
        self.check_environment_cell_capacity(span)?;
        let cloned_env = match env_dict {
            // SAFETY: `env_ptr` targets the closure's environment, which lives in its heap box (stable
            // across `environment` growth) at `place`; `call_value_clone_for_temp` borrows `ctx`, and
            // stack discipline keeps `place` from being mutably aliased during the call.
            Some(dict) => {
                call_value_clone_for_temp(&mut self.ctx, dict, ValOrMut::Ref(env_ptr), span)?
            }
            None => Value::uninit(),
        };
        let env_idx = self.alloc_cell(cloned_env, span)?.target;
        for i in 0..env_len {
            leading.push(Binding::Place(Place {
                target: env_idx,
                path: vec![i as isize],
            }));
        }

        let call_result = self.exec_resolved_call(
            slots,
            module_id,
            function_id,
            leading,
            env_len,
            arg_ops,
            span,
        );

        // Drop the cloned environment temporary (running the captures' `Value::drop`), then reclaim
        // every cell allocated since the marker (the temporary's husk and the callee's frame). The
        // closure itself is left untouched in `place`.
        let drop_result = if call_result.as_ref().is_err_and(RuntimeError::is_hard_abort) {
            self.discard_place_storage(&Place {
                target: env_idx,
                path: vec![],
            });
            Ok(())
        } else {
            match env_dict {
                Some(dict) => {
                    let target = Place {
                        target: env_idx,
                        path: vec![],
                    };
                    match call_value_drop_for_temp(
                        &mut self.ctx,
                        dict,
                        ValOrMut::Mut(target.clone()),
                        span,
                    ) {
                        Ok(ControlFlow::Continue(v)) => {
                            v.discard_storage();
                            Ok(())
                        }
                        Ok(ControlFlow::Transfer(_)) => {
                            panic!("unexpected control transfer from a closure environment drop")
                        }
                        Err(err) => {
                            // A failed semantic drop leaves its target live or partially dropped.
                            // Reclaim the temporary's Rust backing storage explicitly before
                            // `restore_stack`: the stack-restore assertion is reserved for genuine SSA
                            // lowering leaks, not an already-observed cleanup failure.
                            self.discard_place_storage(&target);
                            Err(err)
                        }
                    }
                }
                None => Ok(()),
            }
        };
        self.restore_stack(marker);

        match (call_result, drop_result) {
            (Ok(()), Ok(())) => Ok(()),
            (Ok(()), Err(error)) | (Err(error), Ok(())) => Err(error),
            (Err(initial), Err(during_cleanup)) => Err(self.ctx.poison(initial, during_cleanup)),
        }
    }

    /// Builds a closure value from the target `function` and its `[hidden_dicts…, captures…,
    /// env_dict?]` operands (the `build_closure` layout). The hidden dictionary operands become the
    /// closure's `hidden_args` (interned evidence — a `TraitDictionary` id, or a subscript value
    /// read from its place); the capture places are loaded into the environment tuple; the trailing
    /// symbolic `env_dict` operand becomes the `Value` dictionary that clones/drops that environment.
    fn exec_build_closure(
        &mut self,
        slots: &mut FxHashMap<ssa::Value, Binding>,
        operands: &[ssa::Value],
        function: &FunctionId,
        num_hidden_dicts: usize,
        has_env_dict: bool,
    ) -> Result<Value, RuntimeError> {
        let (hidden_ops, rest) = operands.split_at(num_hidden_dicts);
        let (capture_ops, env_dict_op) = if has_env_dict {
            rest.split_at(rest.len() - 1)
        } else {
            (rest, &[][..])
        };

        // Hidden dictionary/evidence captures → interned `HiddenEvidenceArgValue`s.
        let mut hidden_args: Vec<HiddenEvidenceArgValue> = Vec::with_capacity(hidden_ops.len());
        for op in hidden_ops {
            let arg = match self.try_dict_operand(slots, op) {
                Some(id) => HiddenEvidenceArgValue::TraitDictionary(id),
                None => {
                    // Subscript evidence: a symbolic constant, or a first-class subscript value
                    // carried by a place, read non-consumingly (the place is borrowed evidence,
                    // not owned by the closure).
                    HiddenEvidenceArgValue::Subscript(crate::containers::b(
                        self.subscript_operand(slots, op),
                    ))
                }
            };
            hidden_args.push(arg);
        }

        // Value captures → the owned environment tuple.
        let mut captures: Vec<Value> = Vec::with_capacity(capture_ops.len());
        for op in capture_ops {
            let place = self.place_operand(slots, op);
            captures.push(self.take(&place));
        }

        // The symbolic `Value` dictionary for the captured environment (`None` iff no captures).
        let env_dict = env_dict_op.first().map(|op| self.dict_operand(slots, op));

        let closure = FunctionValue::closure(*function, hidden_args, captures, env_dict);
        Ok(Value::function_value(closure))
    }

    /// Deep-clones the captured environment of the closure at `operand`'s place, mirroring
    /// `eval::eval_clone_closure_env`, and returns the fresh closure value.
    fn exec_clone_closure_env(
        &mut self,
        slots: &FxHashMap<ssa::Value, Binding>,
        operand: &ssa::Value,
        span: Location,
    ) -> Result<Value, RuntimeError> {
        let place = self.place_operand(slots, operand);
        let (function, hidden_args, closure_env_len, env_dict, env_ptr) = {
            let source = place
                .target_ref(&self.ctx)
                .expect("clone_closure_env of an invalid place")
                .as_function()
                .expect("clone_closure_env of a non-function value");
            (
                source.function,
                // Hidden dictionary/evidence is interned evidence (`HiddenEvidenceArgValue`);
                // carry it through to the cloned closure unchanged.
                source.hidden_args.clone(),
                source.closure_env_len,
                source.closure_env_value_dictionary,
                &source.closure_env as *const Value,
            )
        };
        // SAFETY: `env_ptr` targets the source closure's environment, which lives in its heap box
        // (stable across `environment` growth); `call_value_clone_for_temp` borrows `ctx` only.
        let closure_env = match env_dict {
            Some(dict) => {
                call_value_clone_for_temp(&mut self.ctx, dict, ValOrMut::Ref(env_ptr), span)?
            }
            None => Value::unit(),
        };
        Ok(Value::function_value(FunctionValue {
            function,
            hidden_args,
            closure_env,
            closure_env_len,
            closure_env_value_dictionary: env_dict,
        }))
    }

    /// Drops the owned captured environment of the closure at `operand`'s place, mirroring
    /// `eval::eval_drop_closure_env`.
    fn exec_drop_closure_env(
        &mut self,
        slots: &FxHashMap<ssa::Value, Binding>,
        operand: &ssa::Value,
        span: Location,
    ) -> Result<(), RuntimeError> {
        let place = self.place_operand(slots, operand);
        let captured = {
            let target = place
                .target_mut(&mut self.ctx)
                .expect("drop_closure_env of an invalid place");
            let function = target
                .as_function_mut()
                .expect("drop_closure_env of a non-function value");
            function.closure_env_value_dictionary.map(|dict| {
                function.closure_env_len = 0;
                function.closure_env_value_dictionary = None;
                (
                    dict,
                    std::mem::replace(&mut function.closure_env, Value::uninit()),
                )
            })
        };
        let Some((dict, captures)) = captured else {
            return Ok(());
        };
        match call_value_drop_for_temp(&mut self.ctx, dict, ValOrMut::Val(captures), span)? {
            ControlFlow::Continue(v) => v.discard_storage(),
            ControlFlow::Transfer(_) => {
                panic!("unexpected control transfer from a closure environment drop")
            }
        }
        Ok(())
    }

    /// Resolves a `drop` instruction's callee operand to the `(module, function)` it targets, per the
    /// same contract as `call`: either a constant function reference or the **place** of a function
    /// value (e.g. a `Value::drop` method slot projected out of a dictionary), read *by reference*
    /// and never consumed.
    fn callee_target(
        &mut self,
        slots: &mut FxHashMap<ssa::Value, Binding>,
        op: &ssa::Value,
    ) -> (ModuleId, LocalFunctionId) {
        if let ssa::Value::Function(r) = op {
            return (r.module, r.function);
        }
        let place = self.place_operand(slots, op);
        let fv = place
            .target_ref(&self.ctx)
            .expect("drop callee of an invalid place")
            .as_function()
            .expect("drop callee on a non-function value");
        (fv.function.module, fv.function.function)
    }

    /// Builds an uninitialized value with the run-time *shape* of `ty`: a tuple/record/named
    /// aggregate becomes a `Tuple` of (recursively) shaped uninitialized fields, so that
    /// `project`/`store` can address its fields; anything else is a flat `Uninit` cell. (This
    /// mirrors how an `alloca` of aggregate storage yields addressable field slots.) A `Named`
    /// type (e.g. a `struct`) is expanded to its underlying product shape first.
    fn shaped_uninitialized_value(&self, ty: Type) -> Value {
        // Clone the kind out so the type-universe read guard held by `ty.data()` is released before
        // the recursion and (for `Named`) the `instantiated_shape` call below: the latter
        // interns the instantiated shape under a *write* lock, which would deadlock against a still-
        // held read guard.
        let kind = (*ty.data()).clone();
        match kind {
            // Aggregates are seeded as a husk skeleton of (recursively) shaped husk fields, funneled
            // through `aggregate_husk` so a zero-field aggregate (an empty `struct`/record) collapses
            // to a flat `Uninit` rather than `Tuple([])`: never-constructed storage must read back as
            // a husk, while `Tuple([])` is reserved for a *live* empty aggregate written explicitly at
            // construction (see `doc/ssa-uninit-tracking.md`).
            TypeKind::Tuple(elems) => aggregate_husk(
                elems
                    .iter()
                    .map(|e| self.shaped_uninitialized_value(*e))
                    .collect::<Vec<_>>(),
            ),
            TypeKind::Record(fields) => aggregate_husk(
                fields
                    .iter()
                    .map(|(_, t)| self.shaped_uninitialized_value(*t))
                    .collect::<Vec<_>>(),
            ),
            TypeKind::Named(named) => {
                // Resolve the shape in the environment of the module that *defines* the named
                // type, not the currently executing function's module: a named aggregate may be
                // returned across a module boundary, and rooting the env at the wrong module
                // resolves `instantiated_shape` against the wrong (or stale) definition.
                let module = self.session.expect_fresh_module(named.def.module);
                let env = ModuleEnv::new(module, self.session.raw_modules());
                let shape = named.instantiated_shape(&env);
                self.shaped_uninitialized_value(shape)
            }
            _ => Value::uninit(),
        }
    }

    /// Ensures every aggregate step along `place`'s path exists (growing flat-`Uninit` cells into
    /// `Tuple`s with enough `Uninit` leaves), so a subsequent field store can address the leaf.
    ///
    /// First follows `Mut` indirection down to the underlying owned `Val` cell, accumulating the
    /// full field path the same way `Place::target_mut` resolves it (a store through a returned
    /// out-pointer reaches its cell through a `Mut` reference, not a direct `Val`); then grows that
    /// cell. The growth descends through every kind of step `target_mut` can take — tuple fields,
    /// array `Buffer` slots, and variant payloads — so an element store into an array of aggregates
    /// (`[…][i].field`) materializes the still-flat element skeleton in place.
    fn materialize_path(&mut self, place: &Place) {
        let mut index = place.target;
        let mut path: VecDeque<isize> = place.path.iter().copied().collect();
        loop {
            match self.ctx.environment.get(index) {
                Some(ValOrMut::Val(_)) => break,
                Some(ValOrMut::Mut(p)) => {
                    index = p.target;
                    for &i in p.path.iter().rev() {
                        path.push_front(i);
                    }
                }
                // `Ref`/`Dictionary` cells are not owned aggregate storage we can grow into shape;
                // leave addressing them (and any error) to `target_mut`.
                _ => return,
            }
        }
        if path.is_empty() {
            return;
        }
        if let Some(ValOrMut::Val(root)) = self.ctx.environment.get_mut(index) {
            grow_value_to_path(root, path.make_contiguous());
        }
    }

    /// Allocates a fresh environment cell initialized to `init` and returns its place.
    ///
    /// On exhaustion, the current instruction's implicit unwind target runs the ordinary SSA
    /// cleanup pads. Cleanup remains subject to the same quota; a secondary failure while dropping
    /// hard-aborts the unwind, poisons the executor, and bypasses all remaining semantic cleanup.
    fn alloc_cell(&mut self, init: Value, span: Location) -> Result<Place, RuntimeError> {
        if let Err(error) = self.check_environment_cell_capacity(span) {
            init.discard_storage();
            return Err(error);
        }
        let target = self.ctx.environment.len();
        self.ctx.environment.push(ValOrMut::Val(init));
        Ok(Place {
            target,
            path: vec![],
        })
    }

    fn check_environment_cell_capacity(&mut self, span: Location) -> Result<(), RuntimeError> {
        self.ctx
            .check_environment_cell_limit(self.ctx.environment.len(), Some(span))
    }

    /// Reclaims the interpreter backing storage of a completed or unwound script frame.
    ///
    /// SSA cleanup has already performed the frame's semantic drops. Scratch cells may nevertheless
    /// contain abandoned partial constructions when evaluation transferred before producing a value;
    /// reclaiming their Rust storage mirrors `EvalCtx::truncate_environment_storage` in the HIR
    /// interpreter and is distinct from an SSA `stack_restore`, whose live-resource assertion checks
    /// an explicit lowering contract.
    fn reclaim_frame_storage(&mut self, frame_top: usize) {
        self.ctx.truncate_environment_storage(frame_top);
    }

    /// Reclaims one place's boxed interpreter storage without running semantic `Value::drop`.
    ///
    /// This is the reference-interpreter form of abort reclamation: it is only used after semantic
    /// cleanup has already failed, when retrying guest cleanup would be incorrect.
    fn discard_place_storage(&mut self, place: &Place) {
        let target = place
            .target_mut(&mut self.ctx)
            .expect("storage-reclamation target must be addressable");
        let value = std::mem::replace(target, Value::uninit());
        value.discard_storage();
    }

    /// Reclaims register-owned interpreter storage after a frame has become inactive.
    ///
    /// Register ownership and consumption are verified from SSA before execution. Raw reclamation
    /// here only frees the boxed reference-interpreter representation; it makes no semantic
    /// ownership decision. An open projection remains invalid because its accessor epilogue is
    /// semantic cleanup and must have run through an unwind edge before the frame exits.
    fn discard_inactive_bindings(&mut self, slots: FxHashMap<ssa::Value, Binding>) {
        for binding in slots.into_values() {
            match binding {
                Binding::Value(value) => value.discard_storage(),
                Binding::Projected { .. } => {
                    panic!(
                        "SSA frame exited with an open projection; its `end_project` cleanup edge \
                         was not executed"
                    )
                }
                Binding::Place(_) | Binding::Dictionary(_) | Binding::StackMarker(_) => {}
            }
        }
    }

    /// Reclaims SSA-register-owned storage after hard abort without running Ferlium code.
    ///
    /// Ordinary values live in the shared environment, but closure construction and a few
    /// instruction results can temporarily own boxed values in the register map. Open projections
    /// additionally own suspended accessor frames. Pads normally consume both; hard abort bypasses
    /// pads, so host-controlled reclamation must visit these roots explicitly.
    fn discard_bindings_after_hard_abort(&mut self, slots: FxHashMap<ssa::Value, Binding>) {
        let mut suspended = Vec::new();
        for binding in slots.into_values() {
            match binding {
                Binding::Value(value) => value.discard_storage(),
                Binding::Projected { frame, .. } => suspended.push(*frame),
                Binding::Place(_) | Binding::Dictionary(_) | Binding::StackMarker(_) => {}
            }
        }

        // Nested projections occupy successively higher environment ranges. Reclaim the innermost
        // frames first so truncating an outer frame cannot invalidate a still-to-be-visited root.
        suspended.sort_unstable_by_key(|frame| std::cmp::Reverse(frame.frame_top));
        for frame in suspended {
            self.discard_bindings_after_hard_abort(frame.slots);
            self.ctx.call_depth = self
                .ctx
                .call_depth
                .checked_sub(1)
                .expect("a suspended accessor must contribute one live call frame");
            self.reclaim_frame_storage(frame.frame_top);
        }
    }

    /// Resets the top of the stack to `marker`, discarding the storage of every cell allocated
    /// since (a `stack_restore`). Stack discipline guarantees no live place points above `marker`.
    fn restore_stack(&mut self, marker: usize) {
        while self.ctx.environment.len() > marker {
            if let Some(ValOrMut::Val(v)) = self.ctx.environment.pop() {
                // SSA ownership verification proves that stack restoration crosses no live
                // semantic drop obligation. This only frees the boxed interpreter representation.
                v.discard_storage();
            }
        }
    }

    /// Resolves a stack-marker operand to the saved `environment` length it carries.
    fn stack_marker_operand(
        &self,
        slots: &FxHashMap<ssa::Value, Binding>,
        v: &ssa::Value,
    ) -> usize {
        match slots.get(v) {
            Some(Binding::StackMarker(m)) => *m,
            _ => panic!("operand {v} is not bound to a stack marker"),
        }
    }

    /// Resolves a symbolic dictionary operand to its interned `TraitDictionaryId`, if it is one: a
    /// constant `Dictionary(id)`, or a `Parameter`/`Register` bound to `Binding::Dictionary(id)`.
    fn try_dict_operand(
        &self,
        slots: &FxHashMap<ssa::Value, Binding>,
        v: &ssa::Value,
    ) -> Option<TraitDictionaryId> {
        match v {
            ssa::Value::Dictionary(id) => Some(*id),
            ssa::Value::Register(_) | ssa::Value::Parameter(_) => match slots.get(v) {
                Some(Binding::Dictionary(id)) => Some(*id),
                _ => None,
            },
            _ => None,
        }
    }

    /// Resolves a symbolic subscript operand — a constant [`ssa::Value::Subscript`] or the place of
    /// a first-class subscript value (e.g. a forwarded evidence `@extra` parameter) — to its runtime
    /// [`SubscriptValue`], read non-consumingly.
    fn subscript_operand(
        &self,
        slots: &FxHashMap<ssa::Value, Binding>,
        v: &ssa::Value,
    ) -> SubscriptValue {
        if let ssa::Value::Subscript(id) = v {
            return SubscriptValue::bare(*id);
        }
        let place = self.place_operand(slots, v);
        place
            .target_ref(&self.ctx)
            .expect("subscript operand of an invalid place")
            .as_subscript()
            .expect("a subscript operand must resolve to a subscript value")
            .as_ref()
            .clone()
    }

    /// Binds an `@extra` evidence operand at a call boundary: a symbolic trait dictionary binds to
    /// its interned id; a symbolic subscript constant is materialized into a fresh cell holding the
    /// bare subscript value (passed by place, the same shape as forwarded subscript evidence);
    /// anything else is already a place.
    fn evidence_binding(
        &mut self,
        slots: &FxHashMap<ssa::Value, Binding>,
        op: &ssa::Value,
        span: Location,
    ) -> Result<Binding, RuntimeError> {
        if let Some(id) = self.try_dict_operand(slots, op) {
            Ok(Binding::Dictionary(id))
        } else if let ssa::Value::Subscript(id) = op {
            Ok(Binding::Place(
                self.alloc_cell(Value::subscript(*id), span)?,
            ))
        } else {
            Ok(Binding::Place(self.place_operand(slots, op)))
        }
    }

    /// Resolves a symbolic dictionary operand to its interned `TraitDictionaryId`, panicking if the
    /// operand is not a dictionary.
    fn dict_operand(
        &self,
        slots: &FxHashMap<ssa::Value, Binding>,
        v: &ssa::Value,
    ) -> TraitDictionaryId {
        self.try_dict_operand(slots, v)
            .unwrap_or_else(|| panic!("operand {v} is not a symbolic dictionary"))
    }

    /// Resolves a place-typed operand to its `Place`.
    fn place_operand(&self, slots: &FxHashMap<ssa::Value, Binding>, v: &ssa::Value) -> Place {
        match v {
            ssa::Value::Register(_) | ssa::Value::Parameter(_) => match slots.get(v) {
                Some(Binding::Place(p)) => p.clone(),
                // An open scoped projection (a `project` result) is used as the place it exposes,
                // exactly like a `Place` binding, until its `end_project` removes it.
                Some(Binding::Projected { place, .. }) => place.clone(),
                // A place produced by an `AddressorPlace` function (e.g. `buffer_slot`) is bridged
                // through an ordinary value cell as a `PlaceResult` native; unwrap it back to the
                // place it denotes so it can be projected/loaded/stored like any other place.
                Some(Binding::Value(val)) => val
                    .as_primitive_ty::<PlaceResult>()
                    .map(|pr| pr.place().clone())
                    .unwrap_or_else(|| panic!("expected a place but {v} is bound to a value")),
                Some(Binding::StackMarker(_)) => {
                    panic!("expected a place but {v} is bound to a stack marker")
                }
                Some(Binding::Dictionary(_)) => {
                    panic!("expected a place but {v} is bound to a symbolic dictionary")
                }
                None => panic!("unbound place operand {v}"),
            },
            other => panic!("operand {other:?} is not a place"),
        }
    }

    /// Resolves a value-typed operand to an owned `Value` (copying primitives, moving aggregates out
    /// of their register slot).
    fn value_operand(
        &mut self,
        func: &ssa::Function,
        slots: &mut FxHashMap<ssa::Value, Binding>,
        v: &ssa::Value,
    ) -> Value {
        match v {
            ssa::Value::Register(_) | ssa::Value::Parameter(_) => match slots.get(v) {
                // Reading an uninitialized register means a non-trivial value was already moved out
                // by its consuming use and is being read again — a lowering bug, since SSA requires
                // exactly one consuming use. A trivially-copyable scalar/function takes the `Some`
                // (copy) branch and leaves its slot intact, so it may be read any number of times.
                Some(Binding::Value(Value::Uninit)) => panic!(
                    "value operand {v} read after being moved out: a non-trivial value register \
                     must have exactly one consuming use (SSA mis-lowering)"
                ),
                Some(Binding::Value(val)) => match read_copy(val) {
                    Some(copy) => copy,
                    None => match slots.insert(v.clone(), Binding::Value(Value::uninit())) {
                        Some(Binding::Value(moved)) => moved,
                        _ => unreachable!(),
                    },
                },
                Some(Binding::Place(_)) => panic!("expected a value but {v} is bound to a place"),
                Some(Binding::Projected { .. }) => {
                    panic!("expected a value but {v} is bound to an open projection (a place)")
                }
                Some(Binding::StackMarker(_)) => {
                    panic!("expected a value but {v} is bound to a stack marker")
                }
                Some(Binding::Dictionary(_)) => {
                    panic!("expected a value but {v} is bound to a symbolic dictionary")
                }
                None => panic!("unbound value operand {v}"),
            },
            constant => self.constant_value(func, constant),
        }
    }

    /// Materializes a non-register SSA constant as a runtime value.
    fn constant_value(&self, func: &ssa::Function, constant: &ssa::Value) -> Value {
        match constant {
            ssa::Value::Constant(id) => func.constant(*id).representation.clone().into_value(),
            ssa::Value::Function(r) => Value::function(*r),
            ssa::Value::Dictionary(_) => panic!(
                "a symbolic dictionary is evidence, not a value: it is consumed as a dictionary \
                 operand (see `dict_operand`)/call argument, never read with `value_operand`"
            ),
            // A bare static subscript materializes as a first-class subscript value (mirroring
            // `eval`'s `GetSubscript`, which yields `Value::subscript`).
            ssa::Value::Subscript(id) => Value::subscript(*id),
            ssa::Value::Pattern(_) => panic!("compile-time pattern data is not a runtime value"),
            ssa::Value::Register(_) | ssa::Value::Parameter(_) => {
                panic!("{constant} is not an SSA constant")
            }
        }
    }

    /// Borrows a runtime operand for the duration of `use_value`, materializing constants only in
    /// temporary Rust storage. Register/place operands remain borrowed and are never consumed.
    fn with_runtime_value<R>(
        &self,
        func: &ssa::Function,
        slots: &FxHashMap<ssa::Value, Binding>,
        operand: &ssa::Value,
        use_value: impl FnOnce(&Value) -> R,
    ) -> R {
        match operand {
            ssa::Value::Register(_) | ssa::Value::Parameter(_) => match slots.get(operand) {
                Some(Binding::Place(place)) => use_value(
                    place
                        .target_ref(&self.ctx)
                        .expect("comparison of an invalid place"),
                ),
                Some(Binding::Projected { place, .. }) => use_value(
                    place
                        .target_ref(&self.ctx)
                        .expect("comparison of an invalid open projection"),
                ),
                Some(Binding::Value(value)) => use_value(value),
                Some(Binding::StackMarker(_)) => {
                    panic!("comparison operand {operand} is bound to a stack marker")
                }
                Some(Binding::Dictionary(_)) => {
                    panic!("comparison operand {operand} is bound to a symbolic dictionary")
                }
                None => panic!("unbound comparison operand {operand}"),
            },
            _ => {
                let value = self.constant_value(func, operand);
                let result = use_value(&value);
                value.discard_storage();
                result
            }
        }
    }

    /// Returns the immutable literal representation carried by a pattern operand.
    fn pattern_literal_operand(&self, operand: &ssa::Value) -> LiteralValue {
        match operand {
            ssa::Value::Pattern(value) => (**value).clone(),
            other => panic!("comparison pattern operand {other} has no literal representation"),
        }
    }

    /// Reads a representation-copyable value without changing its source place.
    fn load_copy(&self, place: &Place) -> Value {
        read_copy(
            place
                .target_ref(&self.ctx)
                .expect("load of an invalid place"),
        )
        .expect("load source is not representation-copyable; use an ownership move")
    }

    /// Moves a value out of `place` unconditionally, leaving an addressable drop husk behind.
    fn take(&mut self, place: &Place) -> Value {
        let slot = place
            .target_mut(&mut self.ctx)
            .expect("move from an invalid place");
        let husk = husk_like(slot);
        std::mem::replace(slot, husk)
    }

    /// Writes `v` into the cell denoted by `place`. A `store` **drops nothing**; SSA verification
    /// establishes that identifiable local storage carries no live semantic drop obligation.
    fn store(&mut self, v: Value, place: &Place) -> Result<(), RuntimeError> {
        // Generic (`alloca A`) storage starts flat-`Uninit`; a field store grows the enclosing
        // `Tuple` skeleton on demand so the leaf is addressable.
        self.materialize_path(place);
        let slot = place
            .target_mut(&mut self.ctx)
            .expect("store to an invalid place");
        let old = std::mem::replace(slot, v);
        // Reclaims interpreter-only storage (like a stack-pop); runs no `Value::drop`.
        old.discard_storage();
        Ok(())
    }
}

/// Returns a representation copy of `v` iff the boxed interpreter representation may be duplicated
/// by SSA `memcpy`.
///
/// Native opt-in leaves and tuple-backed tuples/records/named structs are copied recursively.
/// Internal place pointers and bare function values are also representation-copyable even though
/// their types do not derive the language-level `TrivialCopy` trait. Strings, arrays, variants,
/// captured functions, and every other owned representation return `None` and must be moved or
/// cloned explicitly. This intentionally depends on representation shape rather than byte size.
fn read_copy(v: &Value) -> Option<Value> {
    if let Some(native) = copy_boxed_trivial_copy_native(v) {
        return Some(native);
    }
    if let Some(place) = v.as_primitive_ty::<PlaceResult>() {
        return Some(Value::native(place.clone()));
    }
    if let Value::Tuple(fields) = v {
        let copied = fields.iter().map(read_copy).collect::<Option<Vec<_>>>()?;
        return Some(Value::tuple(copied));
    }
    // A function value with no captured environment is trivially copyable: the emitter bare-`load`s
    // such values (e.g. a function-typed local, or a `Value::drop`/method loaded from a dictionary)
    // and may read them more than once. A closure that captures an environment is *not* trivially
    // copyable — the emitter clones it through `Value::clone` rather than a bare load — so we fall
    // through to a move for it.
    if let Some(fv) = v.as_function()
        && fv.closure_env_len == 0
    {
        return Some(Value::function_value(FunctionValue {
            function: fv.function,
            hidden_args: fv.hidden_args.clone(),
            closure_env: Value::uninit(),
            closure_env_len: 0,
            closure_env_value_dictionary: None,
        }));
    }
    None
}

/// Grows `value` so the field path `path` is addressable, mirroring how `Place::target_mut` walks
/// the same path. A flat `Uninit` cell met with path still to go is an unmaterialized aggregate
/// leaf and becomes an empty `Tuple` skeleton; from there each step descends like `target_mut`:
///   * `Tuple` — extend with `Uninit` leaves up to the index, recurse into the field;
///   * `Native` `Buffer` (an array's backing storage) — recurse into the indexed slot, so a store
///     into an array element's field (`arr[i].f`) can build the element skeleton in place;
///   * `Variant` at index 0 — recurse into the payload.
///
/// Already-shaped cells are left intact (we only ever *add* `Uninit` leaves, never overwrite data).
fn grow_value_to_path(value: &mut Value, path: &[isize]) {
    let Some((&first, rest)) = path.split_first() else {
        return;
    };
    // A flat `Uninit` cell along the path is an unmaterialized aggregate: grow it into a tuple
    // skeleton so the field becomes addressable. (`Buffer`s and variant payloads are already
    // shaped, so only `Uninit` needs this.) The path is non-empty here (guarded above), so the
    // `Tuple` arm below immediately pushes at least one `Uninit` leaf: this never leaves a bare
    // `Tuple([])`, upholding the empty-aggregate invariant (see `doc/ssa-uninit-tracking.md`).
    if matches!(value, Value::Uninit) {
        *value = Value::tuple(Vec::<Value>::new());
    }
    match value {
        Value::Tuple(fields) => {
            let idx = first as usize;
            while fields.len() <= idx {
                fields.push(Value::uninit());
            }
            grow_value_to_path(&mut fields[idx], rest);
        }
        Value::Native(primitive) => {
            if let Some(buffer) = primitive
                .as_mut()
                .as_mut_any()
                .downcast_mut::<buffer::Buffer>()
                && let Some(slot) = buffer.get_mut_signed(first)
            {
                grow_value_to_path(slot, rest);
            }
        }
        Value::Variant(variant) if first == 0 => {
            grow_value_to_path(&mut variant.value, rest);
        }
        _ => {}
    }
}

/// Wraps the husk skeletons of an aggregate's `fields` into a husk value.
///
/// This is **the** chokepoint for the empty-aggregate invariant (see `doc/ssa-uninit-tracking.md`):
/// a zero-field aggregate husk collapses to a flat `Uninit`, never `Tuple([])`. `Tuple([])` is
/// reserved for a *live* empty aggregate (an empty `struct`/record), so no husk may ever be one —
/// otherwise never-constructed or already-drained storage would look live and be dropped. Every
/// husk-skeleton builder funnels empties through here, so the invariant holds by construction rather
/// than by remembering to special-case empties at each site.
fn aggregate_husk(fields: Vec<Value>) -> Value {
    if fields.is_empty() {
        Value::uninit()
    } else {
        Value::tuple(fields)
    }
}

/// Returns `true` iff `v` is a *husk* — it carries nothing live to drop: a flat `Uninit`, or a
/// non-empty aggregate whose every leaf is (recursively) a husk. Used by `exec_drop` to run each
/// `Value::drop` at most once.
///
/// This is the one site that *reads* the empty-aggregate invariant (`aggregate_husk` enforces the
/// other half): a `Tuple([])` is **live**, not a husk. A zero-field aggregate has no leaf in which to
/// record liveness, so a live one is `Tuple([])` while a husked one is flat `Uninit`; the
/// `!fields.is_empty()` guard keeps the vacuously-true `[].iter().all(..)` from misclassifying a
/// constructed empty struct as a husk (which would skip its `Value::drop`, diverging from the HIR
/// interpreter — see `doc/ssa-uninit-tracking.md`).
fn is_drop_husk(v: &Value) -> bool {
    match v {
        Value::Uninit => true,
        Value::Tuple(fields) => !fields.is_empty() && fields.iter().all(is_drop_husk),
        _ => false,
    }
}

/// Returns a husk mirroring the aggregate *skeleton* of `v`: a `Tuple` becomes a `Tuple` of
/// (recursively) husked leaves — collapsing to flat `Uninit` when empty, via `aggregate_husk` —
/// and anything else becomes a flat `Uninit`. Used to leave drained storage reinitializable
/// field-by-field after a drop, while guaranteeing it reads back as a husk (so it is never dropped
/// twice).
fn husk_like(v: &Value) -> Value {
    match v {
        Value::Tuple(fields) => aggregate_husk(fields.iter().map(husk_like).collect::<Vec<_>>()),
        _ => Value::uninit(),
    }
}

#[cfg(test)]
mod husk_invariant_tests {
    //! Pins the empty-aggregate invariant of `doc/ssa-uninit-tracking.md`: a husk is never
    //! `Tuple([])`, which is reserved for a *live* empty aggregate.
    use super::{aggregate_husk, husk_like, is_drop_husk};
    use crate::hir::value::Value;

    /// The chokepoint collapses a zero-field aggregate husk to flat `Uninit`, never `Tuple([])`.
    #[test]
    fn aggregate_husk_collapses_empty_to_uninit() {
        assert!(matches!(aggregate_husk(vec![]), Value::Uninit));
        // A non-empty aggregate husk stays a tuple of husks.
        assert!(matches!(aggregate_husk(vec![Value::uninit()]), Value::Tuple(f) if f.len() == 1));
    }

    /// A live empty aggregate (`Tuple([])`) is **live**, not a husk; a flat `Uninit` and a non-empty
    /// all-`Uninit` skeleton are husks.
    #[test]
    fn is_drop_husk_treats_empty_tuple_as_live() {
        assert!(!is_drop_husk(&Value::empty_tuple()));
        assert!(is_drop_husk(&Value::uninit()));
        assert!(is_drop_husk(&Value::tuple(vec![
            Value::uninit(),
            Value::uninit()
        ])));
        // Any live leaf makes the aggregate live.
        assert!(!is_drop_husk(&Value::tuple(vec![
            Value::uninit(),
            Value::unit()
        ])));
    }

    /// Draining never leaves a `Tuple([])`: an empty live aggregate husks to flat `Uninit`, so the
    /// same storage cannot be dropped twice. A non-empty aggregate keeps its addressable skeleton.
    #[test]
    fn husk_like_flattens_empty_and_reads_back_as_husk() {
        let drained_empty = husk_like(&Value::empty_tuple());
        assert!(matches!(drained_empty, Value::Uninit));
        assert!(is_drop_husk(&drained_empty));

        let drained_pair = husk_like(&Value::tuple(vec![Value::unit(), Value::unit()]));
        assert!(matches!(&drained_pair, Value::Tuple(f) if f.len() == 2));
        assert!(is_drop_husk(&drained_pair));
    }
}
