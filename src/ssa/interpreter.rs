//! A reference interpreter for the SSA form of Ferlium.
//!
//! The interpreter exists to check that `emit_ssa` lowers HIR to *semantically correct* SSA: it
//! runs a lowered [`ssa::Function`] and produces the value the function computes. It reuses the HIR
//! interpreter's memory substrate — an SSA *place* (pointer) is an [`eval::Place`] and the heap is
//! the [`EvalCtx`]'s `environment`. Native (std) callees are delegated to the HIR interpreter; SSA
//! (script) callees are interpreted recursively so their own lowering is exercised too.

use std::collections::VecDeque;
use std::rc::Rc;

use rustc_hash::FxHashMap;

use crate::{
    CompilerSession, Location,
    compiler::error::RuntimeErrorKind,
    emit_ssa::build_ssa_function,
    eval::{
        ControlFlow, EvalCtx, Place, PlaceResult, RuntimeError, ValOrMut,
        call_value_clone_for_temp, call_value_drop_for_temp,
    },
    hir::{
        function::{ResolvedArgPassing, ResolvedValueArgPassing},
        value::{FunctionHiddenArgValue, FunctionValue, LiteralValue, Value},
    },
    module::{
        FunctionId, LocalFunctionId, ModuleEnv, ModuleId, TraitDictionaryId, id::Id,
        trait_impl::TraitDictionaryEntry,
    },
    ssa::{self, BlockIdentity, InstructionIdentity, InstructionView, value::FunctionReference},
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
/// A non-trivially-copyable value is *moved* out of its slot by its single consuming use, leaving
/// `Value::Uninit` behind. Reading an uninitialized register afterwards is a lowering bug and panics
/// loudly (see `value_operand`) — the same rule `load` already enforces for memory, so a register
/// holding `Uninit` is never silently re-read.
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
    Goto(BlockIdentity),
    /// Return from the current function (the result is already in the return out-pointer).
    Return,
    /// Resume the unwind that this frame's cleanup pad interrupted: hand the in-flight error back to
    /// the caller so propagation continues up the stack.
    ///
    /// When a fallible call raises, the error does not leave the frame immediately — control is first
    /// diverted to a cleanup pad (the `invoke`'s unwind edge) which runs the frame's drops. That pad
    /// has *paused* the unwind. After the drops, this step (the pad's `resume` terminator) lets it
    /// continue: the same error — stashed when control entered the pad — is returned to the caller,
    /// which catches it at the originating call site and runs its own pad. The error is *continued*,
    /// not newly raised, which is why it is `resume` and not a throw.
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
        block: BlockIdentity,
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
    block: BlockIdentity,
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
        Self {
            ctx: EvalCtx::new(module_id, session),
            session,
            cache: FxHashMap::default(),
        }
    }

    /// Runs the no-argument entry function `main_id` of `module_id` and returns its result value, or
    /// the [`RuntimeError`] it raised. A raised error has already unwound the callee's frames through
    /// their cleanup pads (dropping live locals), so propagating it here leaks nothing live.
    pub fn run_main(
        &mut self,
        module_id: ModuleId,
        main_id: LocalFunctionId,
    ) -> Result<Value, RuntimeError> {
        let key = FunctionKey {
            module: module_id,
            identity: main_id,
        };
        let func = self.function(key);
        assert_eq!(
            func.parameters().len(),
            1,
            "eval_ssa entry function must take no arguments (only the return out-pointer)"
        );
        // The sole parameter is the caller-allocated return out-pointer; shape it from the return
        // type so the callee can `project`/`store` its result fields into it.
        let ret_ty = self
            .session
            .expect_fresh_module(module_id)
            .get_function_by_id(main_id)
            .unwrap()
            .definition
            .ty_scheme
            .ty
            .ret;
        let init = self.shaped_uninitialized_value(ret_ty);
        let ret = self.alloc_cell(init);
        self.run_function(key, vec![Binding::Place(ret.clone())])?;
        let slot = ret
            .target_mut(&mut self.ctx)
            .expect("return cell must be addressable");
        Ok(std::mem::replace(slot, Value::uninit()))
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
        #[cfg(debug_assertions)]
        verify_function(&f);
        self.cache.insert(key, f.clone());
        f
    }

    /// Runs `key`'s body with the given parameter bindings (in slot order). The function writes its
    /// result through the return out-pointer parameter, so this returns no value.
    ///
    /// Guards the call depth exactly like the HIR interpreter (`EvalCtx::check_call_depth`): the SSA
    /// interpreter interprets a script callee by *recursing in Rust*, so an unbounded recursion would
    /// overflow the real Rust stack instead of raising [`RuntimeErrorKind::CallDepthLimitExceeded`].
    /// Bounding it at the same `call_depth_limit` keeps the two backends in agreement on deeply
    /// recursive programs.
    fn run_function(&mut self, key: FunctionKey, args: Vec<Binding>) -> Result<(), RuntimeError> {
        if self.ctx.call_depth >= self.ctx.call_depth_limit {
            return Err(RuntimeError::new_native(
                RuntimeErrorKind::CallDepthLimitExceeded {
                    limit: self.ctx.call_depth_limit,
                },
            ));
        }
        self.ctx.call_depth += 1;
        let result = self.run_frame(key, args);
        self.ctx.call_depth -= 1;
        result
    }

    /// Runs one already-depth-checked call frame (see [`run_function`](Self::run_function)). A plain
    /// call frame must run to completion: suspending out of it (a `YieldedOnce` accessor reached
    /// other than through a `project`) is a lowering bug.
    fn run_frame(&mut self, key: FunctionKey, args: Vec<Binding>) -> Result<(), RuntimeError> {
        let func = self.function(key);
        let mut slots: FxHashMap<ssa::Value, Binding> = FxHashMap::default();
        for (i, b) in args.into_iter().enumerate() {
            slots.insert(ssa::Value::Parameter(i), b);
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
        mut block: BlockIdentity,
        mut idx: usize,
    ) -> Result<FrameOutcome, RuntimeError> {
        let mut instructions: Vec<InstructionIdentity> = func.block(block).instructions().collect();
        // The error in flight through this frame's cleanup pads: set when an `invoke` diverts control
        // to its unwind pad, taken when the chain of pads ends in a `resume` that re-raises it. It is
        // always consumed (at `resume`) before the `Err` leaves this frame, so a nested call's own
        // in-flight error never overlaps with this one.
        let mut pending: Option<RuntimeError> = None;
        loop {
            let i = instructions[idx];
            match self.exec(func, &mut slots, &mut pending, i)? {
                Step::Advance => idx += 1,
                Step::Goto(b) => {
                    block = b;
                    instructions = func.block(block).instructions().collect();
                    idx = 0;
                }
                Step::Return => return Ok(FrameOutcome::Completed),
                Step::Resume => {
                    return Err(pending
                        .take()
                        .expect("resume reached without an in-flight error"));
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
        i: InstructionIdentity,
    ) -> Result<Step, RuntimeError> {
        let instr = func.at(i);
        let def = func.definition(i);
        let span = instr.span;
        Ok(match instr.view() {
            InstructionView::Alloca { ty, .. } => {
                let init = self.shaped_uninitialized_value(ty);
                let place = self.alloc_cell(init);
                slots.insert(def.unwrap(), Binding::Place(place));
                Step::Advance
            }
            InstructionView::AllocaPlace { .. } => {
                let place = self.alloc_cell(Value::uninit());
                slots.insert(def.unwrap(), Binding::Place(place));
                Step::Advance
            }
            InstructionView::Subfield { .. } => {
                // The field index is the `int` value at operand `1` — a constant for a static field,
                // or a register holding a run-time offset (loaded from a field-index dictionary
                // parameter for a row-polymorphic record). Either way it resolves to an `isize`.
                let mut place = self.place_operand(slots, &instr.operands[0]);
                let index = self.value_operand(slots, &instr.operands[1]);
                let index = *index
                    .as_primitive_ty::<isize>()
                    .expect("subfield index must be an int");
                place.path.push(index);
                slots.insert(def.unwrap(), Binding::Place(place));
                Step::Advance
            }
            InstructionView::DictEntry { entry_index, .. } => {
                // The symbolic analog of `Subfield`: resolve the dictionary operand to its interned
                // id, read entry `entry_index` (a method function value or an associated const)
                // straight from the impl arena, and materialize it into a fresh cell whose place is
                // bound — so `call`/`drop`/`memcpy` consume it exactly as a `project` result.
                let id = self.dict_operand(slots, &instr.operands[0]);
                let entry = self
                    .ctx
                    .dictionary_value(id)
                    .entry(TraitDictionaryEntryIndex::from_index(entry_index));
                let value = match entry {
                    TraitDictionaryEntry::Method(function) => Value::function(FunctionId {
                        module: id.module_id,
                        function,
                    }),
                    TraitDictionaryEntry::AssociatedConst(lit) => lit.into_value(),
                };
                let place = self.alloc_cell(value);
                slots.insert(def.unwrap(), Binding::Place(place));
                Step::Advance
            }
            InstructionView::Load => {
                let place = self.place_operand(slots, &instr.operands[0]);
                let v = self.load(&place)?;
                slots.insert(def.unwrap(), Binding::Value(v));
                Step::Advance
            }
            InstructionView::Store => {
                let v = self.value_operand(slots, &instr.operands[0]);
                let place = self.place_operand(slots, &instr.operands[1]);
                self.store(v, &place)?;
                Step::Advance
            }
            InstructionView::Memcpy => {
                // A pure copy: the source pointee owns no resource (resource-owning copies are
                // lowered through `Value::clone`), so `load`+`store` duplicates it — and for a
                // scalar pointee `read_copy` leaves the source live. The debug assert enforces that
                // contract: an owned pointee here would be a move mislabeled as a copy (which on a
                // real backend is a shallow copy without drop-cancellation — a double-free / leak).
                let source = self.place_operand(slots, &instr.operands[0]);
                let destination = self.place_operand(slots, &instr.operands[1]);
                debug_assert!(
                    !owns_resources(
                        source
                            .target_ref(&self.ctx)
                            .expect("memcpy of an invalid source place")
                    ),
                    "memcpy of a resource-owning pointee: a copy must be lowered through \
                     Value::clone or emitted as a move (SSA mis-lowering)"
                );
                let v = self.load(&source)?;
                self.store(v, &destination)?;
                Step::Advance
            }
            InstructionView::Move { .. } => {
                // A source-consuming move: read the source place out (leaving it uninitialized) and
                // write it straight into the destination place. The optional layout witness is
                // metadata a backend uses to size the copy; the interpreter moves shape-agnostically
                // and ignores it.
                let source = self.place_operand(slots, &instr.operands[0]);
                let destination = self.place_operand(slots, &instr.operands[1]);
                let v = self.load(&source)?;
                self.store(v, &destination)?;
                Step::Advance
            }
            InstructionView::CompareEqual => {
                // A lowered `match`'s comparison. Both operands are read *non-consumingly*: a
                // scrutinee place is borrowed (never moved), so it stays live for the remaining
                // alternatives and for the arm body, and the literal pattern is materialized. The
                // comparison is `LiteralValue` equality over the snapshots — exactly the HIR
                // interpreter's `eval_case` (`scrutinee.to_literal_value() == pattern`).
                let a = self.operand_literal(slots, &instr.operands[0]);
                let b = self.operand_literal(slots, &instr.operands[1]);
                slots.insert(def.unwrap(), Binding::Value(Value::native(a == b)));
                Step::Advance
            }
            InstructionView::ConditionalBranch {
                on_success,
                on_failure,
            } => {
                let c = self.value_operand(slots, &instr.operands[0]);
                let taken = *c
                    .as_primitive_ty::<bool>()
                    .expect("condbr condition must be a bool");
                Step::Goto(if taken { on_success } else { on_failure })
            }
            InstructionView::UnconditionalBranch { target } => Step::Goto(target),
            InstructionView::Ret => Step::Return,
            InstructionView::Variant { tag } => {
                // Build a tagged variant shell with an uninitialized payload. The constructing site
                // stores it into the variant's destination and then fills the payload in place
                // through a projection of that destination, so the payload aggregate is never
                // materialized into a temporary. A flat `Uninit` payload grows into the right
                // aggregate skeleton on the first field store (see `grow_value_to_path`); a unit
                // payload is written explicitly by the emitter.
                slots.insert(
                    def.unwrap(),
                    Binding::Value(Value::raw_variant(tag, Value::uninit())),
                );
                Step::Advance
            }
            InstructionView::ExtractTag => {
                // Read the variant's tag without consuming it (the payload stays live for the match
                // arms), encoded as the same `int` the HIR interpreter produces.
                let place = self.place_operand(slots, &instr.operands[0]);
                let value = place
                    .target_ref(&self.ctx)
                    .expect("extract_tag of an invalid place");
                let variant = value
                    .as_variant()
                    .expect("extract_tag of a non-variant value");
                let tag = variant.tag_as_isize();
                slots.insert(def.unwrap(), Binding::Value(Value::native(tag)));
                Step::Advance
            }
            InstructionView::Call => {
                self.exec_call(slots, &instr.operands, span)?;
                Step::Advance
            }
            InstructionView::Invoke { normal, unwind } => {
                // A fallible call: on a raised error, stash it and divert to the cleanup pad rather
                // than propagating straight out of the frame. The pad drops this frame's live locals
                // (husk-skipping anything already dropped/moved) and ends in `br <outer pad>` or
                // `resume`, the latter re-raising `pending` to the caller (see the loop in
                // `run_function`). On normal completion control falls through to the continuation.
                match self.exec_call(slots, &instr.operands, span) {
                    Ok(()) => Step::Goto(normal),
                    Err(err) => {
                        *pending = Some(err);
                        Step::Goto(unwind)
                    }
                }
            }
            InstructionView::Resume => Step::Resume,
            InstructionView::Project { ty } => {
                // Enter a scoped subscript: run the accessor to its `yield`, bind the exposed place
                // (and the suspended frame) to this register, and continue with the body.
                self.exec_project(slots, &instr.operands, def.unwrap(), ty)?;
                Step::Advance
            }
            InstructionView::Yield => {
                // Suspend the accessor, exposing the place at operand `0` to the driving `project`.
                let place = self.place_operand(slots, &instr.operands[0]);
                Step::Suspend(place)
            }
            InstructionView::EndProject => {
                // Leave a scoped subscript: resume the accessor's slide to completion and reclaim its
                // frame. Reached on the normal path and inside cleanup pads (epilogue-on-unwind).
                let SuspendedFrame {
                    key,
                    block,
                    idx,
                    slots: acc_slots,
                    frame_top,
                } = match slots.remove(&instr.operands[0]) {
                    Some(Binding::Projected { frame, .. }) => *frame,
                    _ => panic!("end_project operand is not an open projection"),
                };
                let func = self.function(key);
                let result = self.run_loop(&func, acc_slots, block, idx);
                // The accessor frame is torn down whichever way its slide ends: drop the depth it
                // held since the `project` and reclaim its stack cells, then surface any slide error.
                self.ctx.call_depth -= 1;
                self.restore_stack(frame_top);
                match result? {
                    FrameOutcome::Completed => Step::Advance,
                    FrameOutcome::Suspended { .. } => {
                        panic!("a YieldedOnce accessor yielded more than once")
                    }
                }
            }
            InstructionView::Drop => {
                self.exec_drop(slots, &instr.operands, span)?;
                Step::Advance
            }
            InstructionView::StackSave => {
                let marker = self.ctx.environment.len();
                slots.insert(def.unwrap(), Binding::StackMarker(marker));
                Step::Advance
            }
            InstructionView::StackRestore => {
                let marker = self.stack_marker_operand(slots, &instr.operands[0]);
                self.restore_stack(marker);
                Step::Advance
            }
            InstructionView::BuildClosure {
                function,
                num_hidden_dicts,
                has_env_dict,
            } => {
                let closure = self.exec_build_closure(
                    slots,
                    &instr.operands,
                    function,
                    num_hidden_dicts,
                    has_env_dict,
                )?;
                slots.insert(def.unwrap(), Binding::Value(closure));
                Step::Advance
            }
            InstructionView::CloneClosureEnv => {
                let cloned = self.exec_clone_closure_env(slots, &instr.operands[0], span)?;
                slots.insert(def.unwrap(), Binding::Value(cloned));
                Step::Advance
            }
            InstructionView::DropClosureEnv => {
                self.exec_drop_closure_env(slots, &instr.operands[0], span)?;
                Step::Advance
            }
        })
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
        if f.code.as_script().is_some() {
            // A script `Value::drop(&mut self)` in the uniform by-pointer ABI: `drop(self, ())`. Its
            // `()` out-pointer starts a husk like any `@ret`; the drop body writes it (discarded after).
            let unit_ret = self.alloc_cell(Value::uninit());
            self.run_function(
                FunctionKey { module, identity },
                vec![Binding::Place(target.clone()), Binding::Place(unit_ret)],
            )?;
        } else {
            // Delegate to the HIR interpreter with the callee's module given explicitly; the
            // delegate rotates its own ambient module internally, so the SSA interpreter never
            // touches `ctx.module_id` (its IR is fully module-resolved).
            let result = self.ctx.call_resolved_function_with_extra(
                FunctionId {
                    module,
                    function: identity,
                },
                vec![],
                vec![ValOrMut::Mut(target.clone())],
                span,
            );
            match result? {
                ControlFlow::Continue(v) => v.discard_storage(),
                ControlFlow::Transfer(_) => panic!("unexpected control transfer from a drop"),
            }
        }
        // Mark the storage uninitialized so it is never dropped or read again, but preserve the
        // aggregate *skeleton* (a `Tuple` of `Uninit` leaves) so the storage can be reinitialized
        // field-by-field via `project`/`store` (as in `p = ...` reassignment).
        let slot = target
            .target_mut(&mut self.ctx)
            .expect("drop target must be addressable");
        let husk = std::mem::replace(slot, Value::uninit());
        let skeleton = husk_like(&husk);
        *target
            .target_mut(&mut self.ctx)
            .expect("drop target must be addressable") = skeleton;
        husk.discard_storage();
        Ok(())
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
            return self.exec_resolved_call(slots, r.module, r.identity, Vec::new(), arg_ops, span);
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
            self.exec_resolved_call(slots, module_id, function_id, Vec::new(), arg_ops, span)
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
    ) -> Result<(), RuntimeError> {
        // A subscript accessor is always a direct static reference to its (script) member function.
        let key = match &operands[0] {
            ssa::Value::Function(r) => FunctionKey {
                module: r.module,
                identity: r.identity,
            },
            other => panic!("project callee must be a static function reference, got {other:?}"),
        };

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
        let mut args: Vec<Binding> = Vec::with_capacity(arg_ops.len());
        for (k, op) in arg_ops.iter().enumerate() {
            let binding = match param_tags.get(k) {
                Some(ssa::ParameterTag::Dictionary) => match self.try_dict_operand(slots, op) {
                    Some(id) => Binding::Dictionary(id),
                    None => Binding::Place(self.place_operand(slots, op)),
                },
                _ => Binding::Place(self.place_operand(slots, op)),
            };
            args.push(binding);
        }

        // Enter the accessor frame (depth-guarded like `run_function`), recording the stack top so
        // `end_project` can later reclaim the accessor's cells.
        if self.ctx.call_depth >= self.ctx.call_depth_limit {
            return Err(RuntimeError::new_native(
                RuntimeErrorKind::CallDepthLimitExceeded {
                    limit: self.ctx.call_depth_limit,
                },
            ));
        }
        self.ctx.call_depth += 1;
        let frame_top = self.ctx.environment.len();
        let func = self.function(key);
        let mut acc_slots: FxHashMap<ssa::Value, Binding> = FxHashMap::default();
        for (i, b) in args.into_iter().enumerate() {
            acc_slots.insert(ssa::Value::Parameter(i), b);
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
                Err(err)
            }
        }
    }

    /// Pairs each by-pointer-bound parameter with the place it was bound to, for the call-boundary
    /// contract check. `Dictionary`-interned bindings (a symbolic trait dictionary, which has no
    /// pointee) are dropped; everything place-bound — visible arguments, the return out-pointer, and
    /// field-index evidence — is kept with its tag.
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
    /// Evidence (an interned dictionary or a field-index `int`) is not value storage and is skipped.
    #[cfg(debug_assertions)]
    fn check_call_boundary(&self, boundary: &[(ssa::ParameterTag, Place)], phase: CallPhase) {
        for (tag, place) in boundary {
            // Read the pointee. A place that projects through (or ends at) uninitialized storage has
            // no value to read — `boundary_pointee` returns `None`, which the check treats as a husk
            // (the slot is simply not initialized).
            let is_husk = self.boundary_pointee(place).map_or(true, is_drop_husk);
            match tag {
                // A `&mut`/`&`/trivial-copy argument must point at a live value, before and after.
                ssa::ParameterTag::Parameter(passing) => assert!(
                    !is_husk,
                    "SSA call boundary: an argument passed as {passing:?} is a husk {phase} the \
                     call; a `&mut`/`&`/trivial-copy argument must point at a live value",
                ),
                // The return out-pointer must be fully initialized when the callee returns normally.
                // (There is no *precondition* on `@ret` here: a resource-owning `@ret` being
                // overwritten is caught precisely by the `store` discard invariant, and overwriting a
                // resource-free slot — e.g. the in-place `a = a + b` — is sound.)
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
    /// the return out-pointer).
    fn exec_resolved_call(
        &mut self,
        slots: &mut FxHashMap<ssa::Value, Binding>,
        callee_module: ModuleId,
        callee_identity: LocalFunctionId,
        leading: Vec<Binding>,
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
                    // field-index evidence (an `int` passed by place) — both share the `Dictionary`
                    // tag, so the operand disambiguates them. A non-extra (visible/return) parameter
                    // is always a by-pointer place, never reinterpreted as a dictionary.
                    Some(ssa::ParameterTag::Dictionary) => match self.try_dict_operand(slots, op) {
                        Some(id) => Binding::Dictionary(id),
                        None => Binding::Place(self.place_operand(slots, op)),
                    },
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

        // A closure over a *native* function would have to prepend its environment ahead of the
        // native's visible arguments; this is not needed yet (lambda bodies are always scripts).
        assert!(
            leading.is_empty(),
            "a closure over a native function is not lowered to SSA yet"
        );

        // Native callee: marshal the extra (dictionary) arguments and the visible arguments,
        // delegate to the HIR interpreter, then write the returned value through the return
        // out-pointer.
        //
        // A call's operands are laid out as `[extra dictionaries…, visible args…, return
        // out-pointer]`. `parameter_passing` describes only the visible arguments, so the leading
        // `extra_count` operands are the extra (dictionary) parameters the native expects ahead of
        // its visible arguments.
        let passing = f.parameter_passing.clone();
        let n_vis = passing.len();
        let extra_count = arg_ops.len().checked_sub(n_vis + 1).expect(
            "a native call must pass the visible arguments and a return out-pointer at minimum",
        );
        let (extra_ops, rest) = arg_ops.split_at(extra_count);
        let (visible_ops, ret_op) = rest.split_at(n_vis);
        let ret_place = self.place_operand(slots, &ret_op[0]);

        let mut args: Vec<ValOrMut> = Vec::with_capacity(extra_count + n_vis);
        // Extra arguments: a symbolic trait dictionary is passed as interned evidence
        // (`ValOrMut::Dictionary`), exactly as the HIR interpreter passes a dictionary; field-index
        // evidence (an `int`) is passed by reference to its place.
        for op in extra_ops {
            let arg = match self.try_dict_operand(slots, op) {
                Some(id) => ValOrMut::Dictionary(id),
                None => ValOrMut::Mut(self.place_operand(slots, op)),
            };
            args.push(arg);
        }
        // Visible arguments, marshaled per the callee's resolved passing.
        for (arg_passing, op) in passing.iter().zip(visible_ops) {
            let place = self.place_operand(slots, op);
            match arg_passing {
                ResolvedArgPassing::Value(ResolvedValueArgPassing::TrivialCopy) => {
                    args.push(ValOrMut::Val(self.load(&place)?));
                }
                ResolvedArgPassing::Value(ResolvedValueArgPassing::SharedRef)
                | ResolvedArgPassing::MutableRef => {
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

        // The marker captured before allocating any temporary (the hidden field-index evidence
        // cells and the cloned environment) lets us reclaim them — and the callee's frame storage —
        // afterwards.
        let marker = self.ctx.environment.len();

        // Prepend the closure's hidden `@extra` dictionary evidence, in signature order: a trait
        // dictionary binds to its interned id; field-index evidence is materialized into an `int`
        // cell and passed by place. These come ahead of the environment slots, matching the lambda
        // signature `[@extra dicts…, captures…, visible…, ret]`.
        let mut leading: Vec<Binding> = Vec::with_capacity(hidden_args.len() + env_len);
        for arg in &hidden_args {
            match arg {
                FunctionHiddenArgValue::TraitDictionary(id) => {
                    leading.push(Binding::Dictionary(*id));
                }
                FunctionHiddenArgValue::FieldIndex(index) => {
                    let place = self.alloc_cell(Value::native(*index));
                    leading.push(Binding::Place(place));
                }
            }
        }

        // Clone the captured environment into a fresh environment temporary. `env_ptr` points into
        // the closure's heap box (stable across `environment` growth).
        let cloned_env = match env_dict {
            // SAFETY: `env_ptr` targets the closure's environment, which lives in its heap box (stable
            // across `environment` growth) at `place`; `call_value_clone_for_temp` borrows `ctx`, and
            // stack discipline keeps `place` from being mutably aliased during the call.
            Some(dict) => {
                call_value_clone_for_temp(&mut self.ctx, dict, ValOrMut::Ref(env_ptr), span)?
            }
            None => Value::uninit(),
        };
        let env_idx = self.alloc_cell(cloned_env).target;
        for i in 0..env_len {
            leading.push(Binding::Place(Place {
                target: env_idx,
                path: vec![i as isize],
            }));
        }

        let call_result =
            self.exec_resolved_call(slots, module_id, function_id, leading, arg_ops, span);

        // Drop the cloned environment temporary (running the captures' `Value::drop`), then reclaim
        // every cell allocated since the marker (the temporary's husk and the callee's frame). The
        // closure itself is left untouched in `place`.
        let drop_result = match env_dict {
            Some(dict) => {
                let target = Place {
                    target: env_idx,
                    path: vec![],
                };
                match call_value_drop_for_temp(&mut self.ctx, dict, ValOrMut::Mut(target), span) {
                    Ok(ControlFlow::Continue(v)) => {
                        v.discard_storage();
                        Ok(())
                    }
                    Ok(ControlFlow::Transfer(_)) => {
                        panic!("unexpected control transfer from a closure environment drop")
                    }
                    Err(err) => Err(err),
                }
            }
            None => Ok(()),
        };
        self.restore_stack(marker);

        call_result.and(drop_result)
    }

    /// Builds a closure value from the target `function` and its `[hidden_dicts…, captures…,
    /// env_dict?]` operands (the `build_closure` layout). The hidden dictionary operands become the
    /// closure's `hidden_args` (interned evidence — a `TraitDictionary` id, or a `FieldIndex` read
    /// from an `int` place); the capture places are loaded into the environment tuple; the trailing
    /// symbolic `env_dict` operand becomes the `Value` dictionary that clones/drops that environment.
    fn exec_build_closure(
        &mut self,
        slots: &mut FxHashMap<ssa::Value, Binding>,
        operands: &[ssa::Value],
        function: &FunctionReference,
        num_hidden_dicts: usize,
        has_env_dict: bool,
    ) -> Result<Value, RuntimeError> {
        let (hidden_ops, rest) = operands.split_at(num_hidden_dicts);
        let (capture_ops, env_dict_op) = if has_env_dict {
            rest.split_at(rest.len() - 1)
        } else {
            (rest, &[][..])
        };

        // Hidden dictionary/evidence captures → interned `FunctionHiddenArgValue`s.
        let mut hidden_args: Vec<FunctionHiddenArgValue> = Vec::with_capacity(hidden_ops.len());
        for op in hidden_ops {
            let arg = match self.try_dict_operand(slots, op) {
                Some(id) => FunctionHiddenArgValue::TraitDictionary(id),
                None => {
                    // Field-index evidence: an `int` carried by a place.
                    let place = self.place_operand(slots, op);
                    let index = *self
                        .load(&place)?
                        .as_primitive_ty::<isize>()
                        .expect("a field-index evidence capture must be an int");
                    FunctionHiddenArgValue::FieldIndex(index)
                }
            };
            hidden_args.push(arg);
        }

        // Value captures → the owned environment tuple.
        let mut captures: Vec<Value> = Vec::with_capacity(capture_ops.len());
        for op in capture_ops {
            let place = self.place_operand(slots, op);
            captures.push(self.load(&place)?);
        }

        // The symbolic `Value` dictionary for the captured environment (`None` iff no captures).
        let env_dict = env_dict_op.first().map(|op| self.dict_operand(slots, op));

        let closure = FunctionValue::closure(
            FunctionId {
                module: function.module,
                function: function.identity,
            },
            hidden_args,
            captures,
            env_dict,
        );
        Ok(Value::function_value(closure))
    }

    /// Deep-clones the captured environment of the closure at `operand`'s place, mirroring
    /// [`eval::eval_clone_closure_env`], and returns the fresh closure value.
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
                // Hidden dictionary/evidence is trivially-copyable evidence (`FunctionHiddenArgValue`
                // is `Copy`); carry it through to the cloned closure unchanged.
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
    /// [`eval::eval_drop_closure_env`].
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
            return (r.module, r.identity);
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

    /// Allocates a fresh heap cell initialized to `init` and returns the place denoting it.
    fn alloc_cell(&mut self, init: Value) -> Place {
        let target = self.ctx.environment.len();
        self.ctx.environment.push(ValOrMut::Val(init));
        Place {
            target,
            path: vec![],
        }
    }

    /// Resets the top of the stack to `marker`, discarding the storage of every cell allocated
    /// since (a `stack_restore`). Stack discipline guarantees no live place points above `marker`.
    fn restore_stack(&mut self, marker: usize) {
        while self.ctx.environment.len() > marker {
            if let Some(ValOrMut::Val(v)) = self.ctx.environment.pop() {
                // Reclaiming storage by popping the stack is the interpreter freeing the Rust value;
                // a real backend only moves the stack pointer and frees nothing. So a cell reclaimed
                // this way must already carry nothing that owns resources — a husk or a
                // `TrivialCopy` value — otherwise the emitter leaked it (it owed an explicit `drop`).
                debug_assert!(
                    is_reclaimable(&v),
                    "SSA leak: stack_restore reclaims a live resource-owning value (a missing \
                     explicit drop): {v:?}",
                );
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
            ssa::Value::Boolean(b) => Value::native(*b),
            ssa::Value::Integer(i) => Value::native(i.to_isize()),
            ssa::Value::Unit => Value::unit(),
            // A `"…"` constant materializes as a *static literal* string: its bytes live in the data
            // segment (`cap == 0`), so it owns no heap and needs no drop (see `owns_resources`).
            ssa::Value::String(s) => Value::native(s.clone().into_static_literal()),
            ssa::Value::Function(r) => Value::function(FunctionId {
                module: r.module,
                function: r.identity,
            }),
            ssa::Value::Uninit(_) => Value::uninit(),
            ssa::Value::Float(f) => Value::native(
                crate::std::math::Float::new(f.into_inner())
                    .expect("an SSA Float constant is always finite"),
            ),
            ssa::Value::Dictionary(_) => panic!(
                "a symbolic dictionary is evidence, not a value: it is consumed as a dictionary \
                 operand (see `dict_operand`)/call argument, never read with `value_operand`"
            ),
            // The *only* `Literal` ever read as a value operand is the live empty-aggregate marker
            // (`Tuple([])`) that `lower_aggregate_into` stores to construct an empty `struct`/record
            // (see `doc/ssa-uninit-tracking.md`). A `comp_eq` pattern literal — the other producer of
            // `ssa::Value::Literal` — is read non-consumingly through `operand_literal` and never
            // materialized here. The assertion keeps that invariant load-bearing: a stray non-empty
            // literal reaching this arm is a lowering bug, not something to silently materialize.
            ssa::Value::Literal(lit) => {
                debug_assert!(
                    matches!(&**lit, LiteralValue::Tuple(fields) if fields.is_empty()),
                    "the only Literal value operand is the empty-aggregate marker, got {lit:?}"
                );
                (**lit).clone().into_value()
            }
        }
    }

    /// Snapshots a `comp_eq` operand to its `LiteralValue` *without consuming it*: a place operand is
    /// borrowed (`target_ref`), a value-bound register is borrowed, and a constant is materialized.
    /// `match` must never move its scrutinee — it stays live for the remaining alternatives and the
    /// arm body — so this mirrors the HIR interpreter's `eval_case`, which reads the scrutinee by
    /// reference and compares its `to_literal_value()`.
    fn operand_literal(
        // todo do part-wise comparison instead
        &self,
        slots: &FxHashMap<ssa::Value, Binding>,
        v: &ssa::Value,
    ) -> LiteralValue {
        let literal = match v {
            ssa::Value::Register(_) | ssa::Value::Parameter(_) => match slots.get(v) {
                Some(Binding::Place(p)) => p
                    .target_ref(&self.ctx)
                    .expect("comp_eq of an invalid place")
                    .to_literal_value(),
                Some(Binding::Projected { place, .. }) => place
                    .target_ref(&self.ctx)
                    .expect("comp_eq of an invalid open projection")
                    .to_literal_value(),
                Some(Binding::Value(val)) => val.to_literal_value(),
                Some(Binding::StackMarker(_)) => {
                    panic!("comp_eq operand {v} is bound to a stack marker")
                }
                Some(Binding::Dictionary(_)) => {
                    panic!("comp_eq operand {v} is bound to a symbolic dictionary")
                }
                None => panic!("unbound comp_eq operand {v}"),
            },
            ssa::Value::Boolean(b) => Some(LiteralValue::new_native(*b)),
            ssa::Value::Integer(i) => Some(LiteralValue::new_native(i.to_isize())),
            ssa::Value::Unit => Some(LiteralValue::new_native(())),
            ssa::Value::String(s) => Some(LiteralValue::new_native(s.clone())),
            ssa::Value::Literal(lit) => Some((**lit).clone()),
            other => panic!("comp_eq operand {other} has no literal form"),
        };
        literal.expect("comp_eq operand value has no literal form (e.g. a float or function)")
    }

    /// Reads the value at `place`, copying a trivially copyable value or moving a non-trivial one
    /// out of memory (leaving the cell uninitialized).
    fn load(&mut self, place: &Place) -> Result<Value, RuntimeError> {
        let copy = read_copy(
            place
                .target_ref(&self.ctx)
                .expect("load of an invalid place"),
        );
        Ok(match copy {
            Some(v) => v,
            None => {
                let slot = place
                    .target_mut(&mut self.ctx)
                    .expect("load of an invalid place");
                std::mem::replace(slot, Value::uninit())
            }
        })
    }

    /// Writes `v` into the cell denoted by `place`. A `store` **drops nothing**: the overwritten
    /// value must own no resource (a husk or a resource-free in-place reassignment); a resource-owner
    /// here is a leak the emitter owed a `drop` for.
    fn store(&mut self, v: Value, place: &Place) -> Result<(), RuntimeError> {
        // Generic (`alloca A`) storage starts flat-`Uninit`; a field store grows the enclosing
        // `Tuple` skeleton on demand so the leaf is addressable.
        self.materialize_path(place);
        let slot = place
            .target_mut(&mut self.ctx)
            .expect("store to an invalid place");
        let old = std::mem::replace(slot, v);
        debug_assert!(
            is_reclaimable(&old),
            "SSA leak: store overwrites a live resource-owning value (a missing explicit drop): \
             {old:?}",
        );
        // Reclaims interpreter-only storage (like a stack-pop); runs no `Value::drop`.
        old.discard_storage();
        Ok(())
    }
}

/// Returns a copy of `v` iff it is a `TrivialCopy` native scalar (`()`, `bool`, `int`, `float`) —
/// the only values a bare `load` may duplicate. Aggregates, strings, variants, functions, and any
/// owned value return `None` and must be *moved* out of their place instead: the emitter lowers
/// every non-trivial copy through `Value::clone`, never a bare `load`, so a bare `load` of such a
/// value is always a move. (Mirrors `eval::copy_trivial_copy_native_value`, extended with `float`,
/// which is likewise a drop-free scalar.)
fn read_copy(v: &Value) -> Option<Value> {
    if v.as_primitive_ty::<()>().is_some() {
        return Some(Value::unit());
    }
    if let Some(b) = v.as_primitive_ty::<bool>() {
        return Some(Value::native(*b));
    }
    if let Some(i) = v.as_primitive_ty::<isize>() {
        return Some(Value::native(*i));
    }
    if let Some(f) = v.as_primitive_ty::<crate::std::math::Float>() {
        return Some(Value::native(*f));
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

/// Whether `v` owns any resource that an explicit semantic `drop` must release — heap storage (a
/// `string`, an array's `Buffer`, …) or a closure's captured environment — anywhere inside it.
///
/// This is the property the interpreter's `discard_storage` papers over: it frees these Rust values,
/// but a real backend frees nothing on a stack-pop or a slot overwrite. A value that owns *no*
/// resource (a husk; a scalar `int`/`bool`/`float`/`()`; an aggregate or variant built only from
/// such; a bare function) is genuinely free to discard — `read_copy` recognises the trivially-copyable
/// leaves, and the recursion covers aggregates, variants, and closure environments.
fn owns_resources(v: &Value) -> bool {
    match v {
        Value::Uninit => false,
        Value::Tuple(fields) => fields.iter().any(owns_resources),
        Value::Variant(variant) => owns_resources(&variant.value),
        // A closure with a captured environment owns it (released by `drop_closure_env`); a bare
        // function (no environment) owns nothing.
        Value::Function(f) => f.closure_env_len != 0,
        // A *static literal* string owns no heap (its bytes are in the data segment, `cap == 0`), so
        // it is free to discard; an *owned* string owns a heap buffer and must be dropped.
        Value::Native(_) if v.as_primitive_ty::<crate::std::string::String>().is_some() => !v
            .as_primitive_ty::<crate::std::string::String>()
            .unwrap()
            .is_static_literal(),
        // A scalar native (`read_copy` is `Some`) owns nothing; any other native — an array `Buffer`,
        // … — owns heap storage.
        Value::Native(_) => read_copy(v).is_none(),
    }
}

/// Whether `v` can be reclaimed by simply discarding its storage (a stack-pop or a slot overwrite)
/// without leaking — i.e. it [owns no resource](owns_resources). Anything that owns a resource must
/// be released by an explicit semantic `drop`, never silently discarded.
fn is_reclaimable(v: &Value) -> bool {
    !owns_resources(v)
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

/// Verifies the structural well-formedness of a freshly built SSA function (debug builds only),
/// before it is executed or cached.
///
/// A real backend (or this interpreter) would exhibit undefined behavior on malformed IR — falling
/// off the end of a block, jumping into an empty block, or indexing a missing operand. This pass
/// turns each such case into an immediate, precisely-located panic at build time:
///
/// - every instruction satisfies its operand contract ([`ssa::Instruction::verify`]);
/// - a *terminator* appears exactly once per non-empty block, as its last instruction, and no other
///   instruction terminates (so control neither falls off the end nor stops mid-block);
/// - every branch target is an existing, non-empty block (so execution always lands on a real
///   instruction), and the entry block is non-empty.
#[cfg(debug_assertions)]
fn verify_function(func: &ssa::Function) {
    let block_ids: Vec<BlockIdentity> = func.blocks().collect();

    let non_empty = |b: BlockIdentity| !func.block(b).is_empty();
    let target_ok = |b: BlockIdentity| block_ids.contains(&b) && non_empty(b);

    assert!(
        non_empty(func.entry()),
        "SSA function `{}`: the entry block is empty",
        func.name
    );

    for b in &block_ids {
        let b = *b;
        let instructions: Vec<InstructionIdentity> = func.block(b).instructions().collect();
        // Every block must be non-empty and therefore (with the terminator-iff-last check below) end
        // in a terminator: an empty block is a malformed CFG. The emitter allocates blocks before
        // filling them, but always fills them (with code, a fall-through `br`, or the trailing `ret`
        // at finalization), so a leftover empty block is a lowering bug, not a tolerated state.
        assert!(
            !instructions.is_empty(),
            "SSA function `{}` block {}: a block must not be empty (it must end in a terminator)",
            func.name,
            b.raw()
        );
        let last = instructions.len() - 1;
        for (k, &i) in instructions.iter().enumerate() {
            let instr = func.at(i);
            instr.verify();
            assert_eq!(
                instr.is_terminator(),
                k == last,
                "SSA function `{}` block {}: a terminator must be the block's last instruction and \
                 appear exactly once (instruction {} of {})",
                func.name,
                b.raw(),
                k,
                instructions.len()
            );
        }
        // The last instruction terminates (checked above); validate its branch targets.
        match func.at(instructions[last]).view() {
            InstructionView::ConditionalBranch {
                on_success,
                on_failure,
            } => assert!(
                target_ok(on_success) && target_ok(on_failure),
                "SSA function `{}` block {}: condbr targets a missing or empty block",
                func.name,
                b.raw()
            ),
            InstructionView::UnconditionalBranch { target } => assert!(
                target_ok(target),
                "SSA function `{}` block {}: br targets a missing or empty block",
                func.name,
                b.raw()
            ),
            InstructionView::Invoke { normal, unwind } => assert!(
                target_ok(normal) && target_ok(unwind),
                "SSA function `{}` block {}: invoke targets a missing or empty block",
                func.name,
                b.raw()
            ),
            _ => {}
        }
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
