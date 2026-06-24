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
    eval::{ControlFlow, EvalCtx, Place, PlaceResult, RuntimeError, ValOrMut},
    hir::{
        function::{ResolvedArgPassing, ResolvedValueArgPassing},
        value::{FunctionValue, LiteralValue, Value},
    },
    module::{LocalFunctionId, ModuleEnv, ModuleId},
    ssa::{self, BlockIdentity, InstructionIdentity, InstructionView},
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
    fn exec_call(
        &mut self,
        slots: &mut FxHashMap<ssa::Value, Binding>,
        operands: &[ssa::Value],
        span: Location,
    ) -> Result<(), RuntimeError> {
        let (callee_module, callee_identity) = self.callee_target(slots, &operands[0]);
        let key = FunctionKey {
            module: callee_module,
            identity: callee_identity,
        };
        let arg_ops = &operands[1..];

        let module = self.session.expect_fresh_module(callee_module);
        let f = module
            .get_function_by_id(callee_identity)
            .expect("callee function not found");
        let is_script = f.code.as_script().is_some();

        if is_script {
            // Uniform by-pointer ABI: pass the argument places straight through (the last is the
            // callee's return out-pointer), then interpret the callee.
            let args: Vec<Binding> = arg_ops
                .iter()
                .map(|op| Binding::Place(self.place_operand(slots, op)))
                .collect();
            self.run_function(key, args)?;
            return Ok(());
        }

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

    /// Resolves a call's callee operand to the `(module, function)` it targets. The callee may be a
    /// constant function reference or a register/parameter holding a first-class function value (an
    /// indirect call, e.g., a method loaded from a dictionary).
    fn callee_target(
        &mut self,
        slots: &mut FxHashMap<ssa::Value, Binding>,
        op: &ssa::Value,
    ) -> (ModuleId, LocalFunctionId) {
        if let ssa::Value::Function(r) = op {
            return (r.module, r.identity);
        }
        let v = self.value_operand(slots, op);
        let target = v
            .as_function()
            .map(|fv| (fv.module_id, fv.function_id))
            .expect("indirect call on a non-function value");
        v.discard_storage();
        target
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
            ssa::Value::Literal(lit) => (**lit).clone().into_value(),
            ssa::Value::UnitPlace => panic!("&() is a place, not a value"),
        }
    }

    /// Snapshots a `comp_eq` operand to its `LiteralValue` *without consuming it*: a place operand is
    /// borrowed (`target_ref`), a value-bound register is borrowed, and a constant is materialized.
    /// `match` must never move its scrutinee — it stays live for the remaining alternatives and the
    /// arm body — so this mirrors the HIR interpreter's `eval_case`, which reads the scrutinee by
    /// reference and compares its `to_literal_value()`.
    fn operand_literal(
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

