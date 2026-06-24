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
    emit_ssa::build_ssa_function,
    eval::{
        ControlFlow, EvalCtx, Place, PlaceResult, RuntimeError, ValOrMut,
        call_value_clone_for_temp, call_value_drop_for_temp,
    },
    hir::{
        function::{ResolvedArgPassing, ResolvedValueArgPassing},
        value::{FunctionValue, LiteralValue, Value},
    },
    module::{LocalFunctionId, ModuleEnv, ModuleId, TraitDictionaryId},
    ssa::{self, BlockIdentity, InstructionIdentity, InstructionView, value::FunctionReference},
    std::buffer,
    types::r#type::{Type, TypeKind},
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
    /// A saved top of the stack (the `environment` length), the result of a `stack_save`.
    StackMarker(usize),
}

/// The control-flow effect of executing a single instruction.
enum Step {
    /// Continue with the next instruction in the block.
    Advance,
    /// Transfer control to the start of the given block.
    Goto(BlockIdentity),
    /// Return from the current function (the result is already in the return out-pointer).
    Return,
}

/// `Place::target` sentinel for the non-dereferenceable unit place (`&()`).
const UNIT_PLACE: usize = usize::MAX;

fn is_unit_place(place: &Place) -> bool {
    place.target == UNIT_PLACE
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

    /// Runs the no-argument entry function `main_id` of `module_id` and returns its result value.
    pub fn run_main(&mut self, module_id: ModuleId, main_id: LocalFunctionId) -> Value {
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
        self.run_function(key, vec![Binding::Place(ret.clone())])
            .expect("SSA interpretation failed");
        let slot = ret
            .target_mut(&mut self.ctx)
            .expect("return cell must be addressable");
        std::mem::replace(slot, Value::uninit())
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
    /// result through the return out-pointer parameter, so this returns no value.
    fn run_function(&mut self, key: FunctionKey, args: Vec<Binding>) -> Result<(), RuntimeError> {
        let func = self.function(key);
        let mut slots: FxHashMap<ssa::Value, Binding> = FxHashMap::default();
        for (i, b) in args.into_iter().enumerate() {
            slots.insert(ssa::Value::Parameter(i), b);
        }

        let mut block = func.entry();
        let mut instructions: Vec<InstructionIdentity> = func.block(block).instructions().collect();
        let mut idx = 0;
        loop {
            let i = instructions[idx];
            match self.exec(func.as_ref(), &mut slots, i)? {
                Step::Advance => idx += 1,
                Step::Goto(b) => {
                    block = b;
                    instructions = func.block(block).instructions().collect();
                    idx = 0;
                }
                Step::Return => return Ok(()),
            }
        }
    }

    /// Executes the instruction `i` of `func` within the current frame `slots`.
    fn exec(
        &mut self,
        func: &ssa::Function,
        slots: &mut FxHashMap<ssa::Value, Binding>,
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
            InstructionView::Project { index, .. } => {
                let mut place = self.place_operand(slots, &instr.operands[0]);
                place.path.push(index as isize);
                slots.insert(def.unwrap(), Binding::Place(place));
                Step::Advance
            }
            InstructionView::ProjectAt { .. } => {
                // Like `Project`, but the field index is read from operand `1` (an `int` register
                // loaded from a field-index dictionary parameter) rather than a static constant.
                let mut place = self.place_operand(slots, &instr.operands[0]);
                let index = self.value_operand(slots, &instr.operands[1]);
                let index = *index
                    .as_primitive_ty::<isize>()
                    .expect("project_at index must be an int");
                place.path.push(index);
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
                // The fused `load`+`store`: read the source place (copying a trivial pointee or
                // moving a non-trivial one out) and write it straight into the destination place.
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
            InstructionView::BuildClosure { function, env_dict } => {
                let closure = self.exec_build_closure(slots, &instr.operands, function, env_dict)?;
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
            is_all_uninit(v)
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
            // A script `Value::drop(&mut self)` in the uniform by-pointer ABI: `drop(self, ())`.
            self.run_function(
                FunctionKey { module, identity },
                vec![
                    Binding::Place(target.clone()),
                    Binding::Place(Place {
                        target: UNIT_PLACE,
                        path: vec![],
                    }),
                ],
            )?;
        } else {
            // Delegate to the HIR interpreter with the callee's module given explicitly; the
            // delegate rotates its own ambient module internally, so the SSA interpreter never
            // touches `ctx.module_id` (its IR is fully module-resolved).
            let result = self.ctx.call_resolved_function_with_extra(
                identity,
                module,
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
        let skeleton = uninit_like(&husk);
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
            return self.exec_resolved_call(slots, r.module, r.identity, &[], arg_ops, span);
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
                fv.module_id,
                fv.function_id,
                fv.closure_env_len != 0 || !fv.hidden_args.is_empty(),
            )
        };
        if is_closure {
            self.exec_closure_call(slots, &place, arg_ops, span)
        } else {
            self.exec_resolved_call(slots, module_id, function_id, &[], arg_ops, span)
        }
    }

    /// Calls the resolved function `(callee_module, callee_identity)` with `env_places` (a closure's
    /// captured-environment slots, empty for a non-closure call) prepended ahead of the visible
    /// arguments `arg_ops` (the last of which is the return out-pointer).
    fn exec_resolved_call(
        &mut self,
        slots: &mut FxHashMap<ssa::Value, Binding>,
        callee_module: ModuleId,
        callee_identity: LocalFunctionId,
        env_places: &[Place],
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
            // Uniform by-pointer ABI: the captured-environment slots (if any) come first, then the
            // argument places straight through (the last is the callee's return out-pointer).
            let mut args: Vec<Binding> = Vec::with_capacity(env_places.len() + arg_ops.len());
            for place in env_places {
                args.push(Binding::Place(place.clone()));
            }
            for op in arg_ops {
                args.push(Binding::Place(self.place_operand(slots, op)));
            }
            self.run_function(key, args)?;
            return Ok(());
        }

        // A closure over a *native* function would have to prepend its environment ahead of the
        // native's visible arguments; this is not needed yet (lambda bodies are always scripts).
        assert!(
            env_places.is_empty(),
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
        // Extra arguments are `Value` dictionaries, materialized as witness-table tuples. Pass each
        // by reference to its place; the native reads the witness table from it (mirroring how the
        // HIR interpreter passes a dictionary by reference). `dictionary_from_arg` distinguishes
        // this form from the HIR's interned-dictionary form.
        for op in extra_ops {
            args.push(ValOrMut::Mut(self.place_operand(slots, op)));
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
            callee_identity,
            callee_module,
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
        let (module_id, function_id, env_len, env_dict, env_ptr) = {
            let fv = place
                .target_ref(&self.ctx)
                .expect("closure call of an invalid place")
                .as_function()
                .expect("closure call on a non-function");
            // Milestone 1 supports value-capturing closures; hidden dictionary evidence is not
            // lowered yet (a generic function or generic-bodied lambda used first-class).
            assert!(
                fv.hidden_args.is_empty(),
                "closure hidden dictionaries are not lowered to SSA yet"
            );
            (
                fv.module_id,
                fv.function_id,
                fv.closure_env_len,
                fv.closure_env_value_dictionary,
                &fv.closure_env as *const Value,
            )
        };

        // Clone the captured environment into a fresh environment temporary. `env_ptr` points into
        // the closure's heap box (stable across `environment` growth). The marker captured before
        // the clone lets us reclaim the temporary — and the callee's frame storage — afterwards.
        let marker = self.ctx.environment.len();
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
        let env_places: Vec<Place> = (0..env_len)
            .map(|i| Place {
                target: env_idx,
                path: vec![i as isize],
            })
            .collect();

        let call_result =
            self.exec_resolved_call(slots, module_id, function_id, &env_places, arg_ops, span);

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

    /// Builds a closure value from the target `function`, the captured-environment places (the
    /// instruction operands, moved into the environment tuple), and the `Value` dictionary
    /// `env_dict` used to clone/drop that environment.
    fn exec_build_closure(
        &mut self,
        slots: &mut FxHashMap<ssa::Value, Binding>,
        operands: &[ssa::Value],
        function: &FunctionReference,
        env_dict: Option<TraitDictionaryId>,
    ) -> Result<Value, RuntimeError> {
        let mut captures: Vec<Value> = Vec::with_capacity(operands.len());
        for op in operands {
            let place = self.place_operand(slots, op);
            captures.push(self.load(&place)?);
        }
        let closure = FunctionValue::closure(
            function.identity,
            function.module,
            vec![],
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
        let (function_id, module_id, closure_env_len, env_dict, env_ptr) = {
            let source = place
                .target_ref(&self.ctx)
                .expect("clone_closure_env of an invalid place")
                .as_function()
                .expect("clone_closure_env of a non-function value");
            (
                source.function_id,
                source.module_id,
                source.closure_env_len,
                source.closure_env_value_dictionary,
                &source.closure_env as *const Value,
            )
        };
        // SAFETY: `env_ptr` targets the source closure's environment, which lives in its heap box
        // (stable across `environment` growth); `call_value_clone_for_temp` borrows `ctx` only.
        let closure_env = match env_dict {
            Some(dict) => call_value_clone_for_temp(&mut self.ctx, dict, ValOrMut::Ref(env_ptr), span)?,
            None => Value::unit(),
        };
        Ok(Value::function_value(FunctionValue {
            function_id,
            module_id,
            hidden_args: vec![],
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
        (fv.module_id, fv.function_id)
    }

    /// Builds an uninitialized value with the run-time *shape* of `ty`: a tuple/record/named
    /// aggregate becomes a `Tuple` of (recursively) shaped uninitialized fields, so that
    /// `project`/`store` can address its fields; anything else is a flat `Uninit` cell. (This
    /// mirrors how an `alloca` of aggregate storage yields addressable field slots.) A `Named`
    /// type (e.g. a `struct`) is expanded to its underlying product shape first.
    fn shaped_uninitialized_value(&self, ty: Type) -> Value {
        // Unit carries no data and is never written through the out-pointer (a unit-typed body
        // stores nothing), so its cell must be seeded with the real native unit value rather than a
        // flat `Uninit`: the result read back is `()`, matching the HIR interpreter.
        if ty == Type::unit() {
            return Value::unit();
        }
        // Clone the kind out so the type-universe read guard held by `ty.data()` is released before
        // the recursion and (for `Named`) the `instantiated_shape` call below: the latter
        // interns the instantiated shape under a *write* lock, which would deadlock against a still-
        // held read guard.
        let kind = (*ty.data()).clone();
        match kind {
            TypeKind::Tuple(elems) => Value::tuple(
                elems
                    .iter()
                    .map(|e| self.shaped_uninitialized_value(*e))
                    .collect::<Vec<_>>(),
            ),
            TypeKind::Record(fields) => Value::tuple(
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

    /// Resolves a place-typed operand to its `Place`.
    fn place_operand(&self, slots: &FxHashMap<ssa::Value, Binding>, v: &ssa::Value) -> Place {
        match v {
            ssa::Value::Register(_) | ssa::Value::Parameter(_) => match slots.get(v) {
                Some(Binding::Place(p)) => p.clone(),
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
                None => panic!("unbound place operand {v}"),
            },
            ssa::Value::UnitPlace => Place {
                target: UNIT_PLACE,
                path: vec![],
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
                Some(Binding::StackMarker(_)) => {
                    panic!("expected a value but {v} is bound to a stack marker")
                }
                None => panic!("unbound value operand {v}"),
            },
            ssa::Value::Boolean(b) => Value::native(*b),
            ssa::Value::Integer(i) => Value::native(i.to_isize()),
            ssa::Value::Unit => Value::unit(),
            ssa::Value::String(s) => Value::native(s.clone()),
            ssa::Value::Function(r) => Value::function(r.identity, r.module),
            ssa::Value::Uninit(_) => Value::uninit(),
            ssa::Value::Float(f) => Value::native(
                crate::std::math::Float::new(f.into_inner())
                    .expect("an SSA Float constant is always finite"),
            ),
            ssa::Value::Dictionary(entries) => {
                // A dictionary is materialized as a tuple of its (bridged) entries: method function
                // references, associated constants, and nested dictionaries.
                let entries = entries.clone();
                let mut vals: Vec<Value> = Vec::with_capacity(entries.len());
                for e in &entries {
                    vals.push(self.value_operand(slots, e));
                }
                Value::tuple(vals)
            }
            ssa::Value::Literal(_) => unreachable!(
                "a `Literal` is only ever a `comp_eq` pattern, read through `operand_literal`"
            ),
            ssa::Value::UnitPlace => panic!("&() is a place, not a value"),
        }
    }

    /// Snapshots a `comp_eq` operand to its `LiteralValue` *without consuming it*: a place operand is
    /// borrowed (`target_ref`), a value-bound register is borrowed, and a constant is materialized.
    /// `match` must never move its scrutinee — it stays live for the remaining alternatives and the
    /// arm body — so this mirrors the HIR interpreter's `eval_case`, which reads the scrutinee by
    /// reference and compares its `to_literal_value()`.
    fn operand_literal(// todo do part-wise comparison instead
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
                Some(Binding::Value(val)) => val.to_literal_value(),
                Some(Binding::StackMarker(_)) => {
                    panic!("comp_eq operand {v} is bound to a stack marker")
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
        if is_unit_place(place) {
            return Ok(Value::unit());
        }
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

    /// Writes `v` into the cell denoted by `place`, discarding any prior contents.
    fn store(&mut self, v: Value, place: &Place) -> Result<(), RuntimeError> {
        if is_unit_place(place) {
            v.discard_storage();
            return Ok(());
        }
        // Generic (`alloca A`) storage is allocated flat-`Uninit` because its concrete aggregate
        // shape is unknown statically. A field store materializes the enclosing `Tuple` skeleton on
        // demand so the leaf is addressable.
        self.materialize_path(place);
        let slot = place
            .target_mut(&mut self.ctx)
            .expect("store to an invalid place");
        let old = std::mem::replace(slot, v);
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
            function_id: fv.function_id,
            module_id: fv.module_id,
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
    // shaped, so only `Uninit` needs this.)
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

/// Returns `true` iff `v` carries nothing live to drop: a flat `Uninit`, or an aggregate whose every
/// leaf is (recursively) uninitialized.
fn is_all_uninit(v: &Value) -> bool {
    match v {
        Value::Uninit => true,
        Value::Tuple(fields) => fields.iter().all(is_all_uninit),
        _ => false,
    }
}

/// Returns an uninitialized value mirroring the aggregate *skeleton* of `v`: a `Tuple` becomes a
/// `Tuple` of (recursively) uninitialized leaves; anything else becomes a flat `Uninit`. Used to
/// leave drained storage reinitializable field-by-field after a drop.
fn uninit_like(v: &Value) -> Value {
    match v {
        Value::Tuple(fields) => Value::tuple(fields.iter().map(uninit_like).collect::<Vec<_>>()),
        _ => Value::uninit(),
    }
}

