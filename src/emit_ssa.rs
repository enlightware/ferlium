use crate::FxHashMap;
use ordered_float::NotNan;
use ustr::Ustr;

use crate::hir::function::ResolvedArgPassing;
use crate::module::{
    ExtraParameterId, ResolvedLocalClone, ResolvedLocalDrop, ResolvedTakeLocalValueMode,
};
use crate::ssa::Instruction;
use crate::ssa::value::ShownType;
use crate::types::r#trait::TraitMethodIndex;
use crate::types::r#type::{FnReturnConvention, FnType};
use crate::{
    CompilerSession, Location, Modules, containers,
    format::FormatWith,
    hir::{
        self, CallArgument, Case, ENode, ENodeArena, Elaborated, GetDictionary, LoopId,
        dictionary::DictionaryReq, value::LiteralValue,
    },
    module::{
        self, FunctionId, LocalDeclId, LocalFunctionId, Module, ModuleEnv, ModuleId,
        TraitDictionaryId, TraitImplId, id::Id,
    },
    ssa::{self, BlockIdentity, value::FunctionReference},
    std::{
        STD_MODULE_ID,
        core_traits_names::VALUE_TRAIT_NAME,
        math::Float,
        value::{VALUE_CLONE_METHOD_INDEX, VALUE_DROP_METHOD_INDEX, type_has_static_layout},
    },
    types::{
        effects::{EffType, Effect, PrimitiveEffect},
        r#type::Type,
    },
};

/// Emits the textual representation of the low-level (aka SSA) ferlium IR of `module`.
///
/// Every lowerable local function of `module` is emitted, including the (anonymous) member
/// functions of its subscripts. A `YieldedOnce` subscript member is emitted standalone as a
/// suspendable function (its `yield` exposes the yielded place to the driving `project`). Only
/// bodiless (native) functions are skipped.
///
/// Intended for testing and debugging.
pub fn emit_ssa(module: &Module, others: &Modules, session: &CompilerSession) -> String {
    let mut functions: Vec<(Ustr, LocalFunctionId)> = (0..module.function_count())
        .map(LocalFunctionId::from_index)
        .filter_map(|id| {
            let f = module.get_function_by_id(id)?;
            // Only script functions have a body to lower.
            f.code.as_ref().as_script()?;
            // A subscript member resolves to its subscript's name; truly anonymous functions are skipped.
            let name = module.get_function_name_by_id(id)?;
            Some((name, id))
        })
        .collect();
    functions.sort_by_key(|(name, id)| (*name, id.as_index()));
    functions
        .into_iter()
        .map(|(_, f)| Emitter::emit_ssa_fn(f, module, others, session))
        .collect::<Vec<_>>()
        .join("\n")
}

/// Returns the SSA value of the pointer-sized signed integer constant `value`.
fn int_constant(value: isize) -> ssa::Value {
    ssa::Value::Integer(containers::b(ssa::value::Integer::from_isize(value)))
}

/// Returns the qualified `"module::function"` name of `f`.
fn function_name(f: LocalFunctionId, module: &Module, others: &Modules) -> Ustr {
    let e = ModuleEnv::new(module, others);
    let qualified_module = others.get_name(module.module_id()).unwrap();
    let function = e.current.get_function_name_by_id(f).unwrap();
    format!("{}::{}", qualified_module, function).into()
}

/// The SSA blocks involved in the lowering of a case in a match expression.
struct CaseBlocks {
    /// The head blocks for the conditions.
    heads: Vec<BlockIdentity>,

    /// The body blocks for the conditions.
    bodies: Vec<BlockIdentity>,

    /// The default case block.
    default: BlockIdentity,

    /// The tail block of the case.
    tail: BlockIdentity,
}

/// A constructor of SSA IR.
struct Emitter<'a> {
    /// The module being lowered.
    module: &'a Module,

    /// The other modules.
    others: &'a Modules,

    /// The context in which the emitter inserts new IR.
    context: InsertionContext,

    /// The HIR node arena.
    hir_arena: &'a ENodeArena,

    /// The current compiler session.
    session: &'a CompilerSession,
}

/// Builds the SSA IR of the function `source` of `module` and returns the lowered function.
///
/// This is the shared entry point used both by the textual SSA dump (`emit_ssa`) and by backends
/// (such as the WASM emitter) that consume the lowered `ssa::Function` directly.
pub fn build_ssa_function(
    source: LocalFunctionId,
    module: &Module,
    others: &Modules,
    session: &CompilerSession,
) -> ssa::Function {
    Emitter::build_ssa_fn(source, module, others, session)
}

impl<'a> Emitter<'a> {
    /// Generates the textual IR of `source`.
    fn emit_ssa_fn(
        source: LocalFunctionId,
        module: &'a Module,
        others: &'a Modules,
        session: &'a CompilerSession,
    ) -> String {
        let lowered = Self::build_ssa_fn(source, module, others, session);
        let env = ModuleEnv::new(module, others);
        format!("{}", lowered.format_with(&env))
    }

    /// Builds and returns the lowered SSA representation of `source`.
    fn build_ssa_fn(
        source: LocalFunctionId,
        module: &'a Module,
        others: &'a Modules,
        session: &'a CompilerSession,
    ) -> ssa::Function {
        let f = module.get_function_by_id(source).unwrap();
        let syntax = f
            .code
            .as_ref()
            .as_script()
            .expect("function should be a script");

        let name = module.get_function_name_by_id(source).unwrap();
        let mut lowered = ssa::Function::new(name);

        // The function signature is laid out as `[extra dictionary/evidence params..., runtime
        // args...]`. Extra parameters occupy the leading slots `[0, extra_count)` and the visible
        // runtime arguments, which are the leading `LocalDecl`s, occupy `[extra_count, ..)`.
        let env = ModuleEnv::new(module, others);
        let extra = f.definition.ty_scheme.extra_parameters(env);
        let extra_count = extra.requirements.len();

        let mut extra_parameters: FxHashMap<ExtraParameterId, ssa::Value> = FxHashMap::default();
        for j in 0..extra_count {
            extra_parameters.insert(ExtraParameterId::from_index(j), ssa::Value::Parameter(j));
        }

        // Record which incoming dictionary parameter witnesses the `Value` layout of each generic
        // type, so that allocations of generic storage can carry their run-time layout witness.
        let value_trait_id = env.expect_std_trait_id(VALUE_TRAIT_NAME);
        let mut value_witnesses: Vec<(Type, ssa::Value)> = vec![];
        for (j, req) in extra.requirements.iter().enumerate() {
            if let DictionaryReq::TraitImpl {
                trait_id,
                input_tys,
                ..
            } = req
                && *trait_id == value_trait_id
                && let [ty] = input_tys[..]
            {
                value_witnesses.push((ty, ssa::Value::Parameter(j)));
            }
        }

        // Record the function signature in slot order: the extra (dictionary/evidence)
        // parameters first, then the visible runtime arguments (the leading `LocalDecl`s).
        for req in &extra.requirements {
            lowered.add_parameter(req.to_dict_type_in_env(&env), ssa::ParameterTag::Dictionary);
        }

        // Bind the runtime argument locals. For a plain function these are exactly the visible
        // arguments; for a lowered closure (lambda) the captured-environment slots come first — they
        // are the leading `LocalDecl`s but are not part of the surface `arg_names` — followed by the
        // visible arguments. The closure's application passes each environment slot's place ahead of
        // the visible argument places, matching this order. Every parameter is passed by pointer (the
        // resolved passing is recorded in the signature only as the obligation a later backend may
        // relax to direct passing per `doc/abi.md`), so each argument local is the place its incoming
        // pointer denotes. `parameter_passing` describes only the visible arguments, so it is indexed
        // relative to the first visible argument.
        let runtime_arg_count = syntax.runtime_arg_count;
        let visible_arg_count = f.definition.arg_names.len();
        let capture_count = runtime_arg_count - visible_arg_count;
        let mut locals: FxHashMap<LocalDeclId, ssa::Value> = FxHashMap::default();
        for i in 0..runtime_arg_count {
            let passing = if i < capture_count {
                // A captured-environment slot is handed to the body as a mutable reference into the
                // (per-call cloned) environment.
                ResolvedArgPassing::MutableRef
            } else {
                f.parameter_passing[i - capture_count]
            };
            lowered.add_parameter(f.locals[i].ty, ssa::ParameterTag::Parameter(passing));
            let param = ssa::Value::Parameter(extra_count + i);
            locals.insert(LocalDeclId::from_index(i), param);
        }

        // Append the return out-pointer as the last parameter. It is present unconditionally, even
        // when the return type is `()`: the function writes its result through this pointer and then
        // returns with no operand.
        let return_type = f.definition.ty_scheme.ty.ret;
        let return_destination =
            ssa::Value::Parameter(lowered.add_parameter(return_type, ssa::ParameterTag::Return));

        // Create the function's entry.
        let entry = lowered.add_block().id();
        let code = &module.hir_arena[syntax.entry_node_id];
        let span = code.span;

        // Instantiate an emitter to generate the function's contents.
        let mut emitter = Emitter {
            module,
            others,
            context: InsertionContext {
                function: lowered,
                source,
                point: InsertionPoint::End(entry),
                span,
                locals,
                extra_parameters,
                value_witnesses,
                loops: FxHashMap::default(),
                return_destination,
                returns_place: f.definition.returns_place(),
                scopes: Vec::new(),
                pending_pads: Vec::new(),
            },
            hir_arena: &module.hir_arena,
            session,
        };

        // Allocate frame storage for every `Owned` local and bind it to its `alloca` place.
        emitter.allocate_owned_locals();

        // Lower the body, dispatching on the function's return convention.
        match f.definition.return_convention() {
            // A value-returning function stores its result into the return out-pointer.
            FnReturnConvention::Value => {
                let ret_dest = emitter.context.return_destination.clone();
                emitter.lower_value_into(code, Some(ret_dest));
            }
            // An addressor function returns a caller-rooted place. Its body is `never`-typed and
            // ends in `return <place-expr>` (enforced at `FunctionDefinition::returns_place`
            // validation); the embedded `Return` stores the place pointer into the return
            // out-pointer. Driving with no destination avoids a spurious value store.
            FnReturnConvention::AddressorPlace => {
                emitter.lower_value_into(code, None);
            }
            // A `YieldedOnce` member is a suspendable accessor: its body is `never`-typed, runs its
            // ramp, and ends (in block-structured position) at a `Yield(place)` that exposes the
            // yielded place and suspends; the instructions after the yield are the slide (epilogue),
            // reached when the driving `WithYielded` resumes via `end_project`. Like an addressor it
            // produces no value, so it is driven with no destination (the `Yield` itself exposes the
            // place; no spurious value store).
            FnReturnConvention::YieldedOnce => {
                emitter.lower_value_into(code, None);
            }
        }

        // Append the trailing `ret`.
        if !emitter.current_block_is_terminated() {
            emitter.insert(Instruction::ret(emitter.context.span));
        }

        // Emit the bodies of any deferred cleanup landing pads. Done last, after the body's final
        // block is terminated, so each pad is filled as a contiguous instruction range (see
        // `fill_pending_pads`).
        emitter.fill_pending_pads();

        emitter.context.function
    }

    /// Returns a reference to the function identified by `f`.
    fn demand_function(&self, f: LocalFunctionId, module_identity: ModuleId) -> FunctionReference {
        let module = self.session.expect_fresh_module(module_identity);
        FunctionReference {
            identity: f,
            name: function_name(f, module, self.others),
            module: module_identity,
        }
    }

    /// Resolves a [`FunctionId`] to the `(LocalFunctionId, ModuleId)` pair identifying the function
    /// within its defining module. `FunctionId` is module-qualified, so this just reads its fields.
    fn resolve_function(&self, function: FunctionId) -> (LocalFunctionId, ModuleId) {
        (function.function, function.module)
    }

    /// Resolves a module-qualified [`TraitImplId`] to a canonical [`TraitDictionaryId`].
    fn dictionary_id(&self, dictionary: TraitImplId) -> TraitDictionaryId {
        TraitDictionaryId {
            module_id: dictionary.module,
            impl_id: dictionary.impl_id,
        }
    }

    /// Lowers an indirect `Value::clone(source, target)` call dispatched through the dictionary
    /// extra parameter `dictionary`.
    ///
    /// `source` is the place of the value to clone, and `target` is the (uninitialized) destination
    /// place the clone initializes. `cloned_ty` is the cloned value's type `T`, used to resolve the
    /// dictionary's `clone` slot. The clone method returns `()`, so a throwaway unit return
    /// out-pointer is appended to the call per the ABI.
    fn lower_value_clone_via_dictionary(
        &mut self,
        span: Location,
        dictionary: ExtraParameterId,
        cloned_ty: Type,
        source: ssa::Value,
        target: ssa::Value,
    ) {
        // The dictionary is a forwarded `@extra` parameter — a symbolic dictionary operand.
        let dictionary = self.context.extra_parameters[&dictionary].clone();
        let (entry_index, method_ty) = self.value_method(VALUE_CLONE_METHOD_INDEX, cloned_ty);
        let method_place = self
            .insert(Instruction::dict_entry(
                span,
                dictionary,
                entry_index,
                method_ty,
            ))
            .unwrap();
        // The callee is the place of the `Value::clone` method entry; the call reads the function
        // value by reference (never loaded into a register — see the `call` contract). A plain
        // `call`, not an `invoke`: `Value::clone` is infallible by its trait contract (a fallible
        // clone impl is a compile error), so the clone can never raise and needs no cleanup pad.
        self.insert(Instruction::call(span, method_place, [source, target]));
    }

    /// Returns the runtime dictionary entry index and function type of the `Value` trait method
    /// `method_index` (e.g. [`VALUE_DROP_METHOD_INDEX`] or [`VALUE_CLONE_METHOD_INDEX`]) for the
    /// type `ty`.
    fn value_method(&self, method_index: TraitMethodIndex, ty: Type) -> (usize, Type) {
        let env = ModuleEnv::new(self.module, self.others);
        let value_trait_id = env.expect_std_trait_id(VALUE_TRAIT_NAME);
        let trait_def = env.trait_def(value_trait_id);
        let dict_ty = trait_def.get_dictionary_type_for_tys(&[ty], &[], &[]);
        let entry_index = trait_def.dictionary_method_index(method_index).as_index();
        let dict_ty_data = dict_ty.data();
        let method_ty = dict_ty_data
            .as_tuple()
            .expect("Value dictionary should be a tuple type")[entry_index];
        (entry_index, method_ty)
    }

    /// Resolves a `ResolvedLocalDrop` to a [`DropSpec`], or `None` when no semantic drop is needed.
    fn resolve_drop(&self, drop: ResolvedLocalDrop) -> Option<DropSpec> {
        match drop {
            ResolvedLocalDrop::Skip => None,
            ResolvedLocalDrop::Static(fid) => {
                let (fi, mi) = self.resolve_function(fid);
                Some(DropSpec::Static(self.demand_function(fi, mi)))
            }
            ResolvedLocalDrop::Dictionary(extra) => Some(DropSpec::Dictionary(extra)),
        }
    }

    /// Emits a single init-guarded `drop` instruction for the obligation `(place, dropped_ty, spec)`,
    /// materializing the `Value::drop` callee (a constant for a static drop, or a dictionary load for
    /// a dictionary drop). Does nothing if the current block is already terminated.
    fn emit_drop(&mut self, span: Location, place: ssa::Value, dropped_ty: Type, spec: DropSpec) {
        if self.current_block_is_terminated() {
            return;
        }
        let callee = match spec {
            DropSpec::Static(fref) => ssa::Value::Function(fref),
            DropSpec::Dictionary(dictionary) => {
                // The dictionary is a forwarded `@extra` parameter — a symbolic dictionary operand.
                let dictionary = self.context.extra_parameters[&dictionary].clone();
                let (entry_index, method_ty) =
                    self.value_method(VALUE_DROP_METHOD_INDEX, dropped_ty);
                // The callee is the place of the `Value::drop` method entry; the `drop` reads the
                // function value by reference (never loaded — same callee contract as `call`).
                self.insert(Instruction::dict_entry(
                    span,
                    dictionary,
                    entry_index,
                    method_ty,
                ))
                .unwrap()
            }
        };
        self.insert(Instruction::drop(span, place, callee));
    }

    /// Pushes a new lexical scope whose drop obligations are the owned, non-`Skip` locals listed in
    /// `cleanup` (in declaration order).
    fn enter_scope(&mut self, cleanup: &[LocalDeclId]) {
        let mut actions = Vec::new();
        for &local in cleanup {
            let decl = self.local_declaration(local);
            if !decl.owns_storage() {
                continue;
            }
            let drop = match decl.local_drop() {
                Some(d) => *d,
                None => continue,
            };
            let dropped_ty = decl.ty;
            let place = self.place_of_local(local);
            if let Some(spec) = self.resolve_drop(drop) {
                actions.push(CleanupAction::Drop(DropObligation {
                    place,
                    dropped_ty,
                    spec,
                }));
            }
        }
        self.context.scopes.push(Scope { actions, pad: None });
    }

    /// Pushes the dedicated scope a `WithYielded` opens: its sole cleanup action is the `end_project`
    /// that runs the accessor slide for the projection `place`. Lowering the body inside this scope
    /// makes the slide run after the body's own drops, on every exit (normal, transfer, error pad).
    fn enter_projection_scope(&mut self, place: ssa::Value) {
        self.context.scopes.push(Scope {
            actions: vec![CleanupAction::EndProject { place }],
            pad: None,
        });
    }

    /// Emits a single cleanup action (a drop, or the `end_project` that runs an accessor slide). Does
    /// nothing if the current block is already terminated, mirroring `emit_drop`.
    fn emit_cleanup(&mut self, span: Location, action: CleanupAction) {
        match action {
            CleanupAction::Drop(o) => self.emit_drop(span, o.place, o.dropped_ty, o.spec),
            CleanupAction::EndProject { place } => {
                if !self.current_block_is_terminated() {
                    self.insert(Instruction::end_project(span, place));
                }
            }
        }
    }

    /// Pops the innermost scope, emitting its cleanup in reverse declaration order (normal scope exit).
    fn exit_scope(&mut self, span: Location) {
        let scope = self
            .context
            .scopes
            .pop()
            .expect("exit_scope without a matching enter_scope");
        for action in scope.actions.into_iter().rev() {
            self.emit_cleanup(span, action);
        }
    }

    /// Returns the lowering targets of the enclosing loop labelled `label`.
    fn loop_frame(&self, label: LoopId) -> LoopFrame {
        self.context
            .loops
            .get(&label)
            .expect("break/continue targets a loop not in scope")
            .clone()
    }

    /// Emits the drops of every scope above `to_depth` (innermost first), for a control transfer
    /// that unwinds out to the scope at depth `to_depth`.
    ///
    /// The scopes are left on the stack: the block becomes terminated by the transfer's following
    /// terminator, so the skipped `exit_scope` calls become no-ops on the dead edge.
    fn emit_unwind_drops(&mut self, span: Location, to_depth: usize) {
        let actions: Vec<CleanupAction> = self.context.scopes[to_depth..]
            .iter()
            .rev()
            .flat_map(|scope| scope.actions.iter().rev().cloned())
            .collect();
        for action in actions {
            self.emit_cleanup(span, action);
        }
    }

    /// Emits the drops of *all* enclosing scopes, innermost first (the unwinding performed by a
    /// `return`).
    fn emit_return_drops(&mut self, span: Location) {
        self.emit_unwind_drops(span, 0);
    }

    /// Allocates (or returns the cached) cleanup pad the current scope's fallible calls should unwind
    /// to, plus the outer pads it chains to. The pad blocks are created empty here and recorded in
    /// `pending_pads`; their bodies are emitted at function finalization (see `fill_pending_pads`),
    /// because a block is a contiguous range in the shared instruction arena and so cannot be filled
    /// in the middle of lowering another block. Returns `None` when no enclosing scope has drop
    /// obligations — the frame has nothing to clean up, so a raised error propagates straight to the
    /// caller and the call stays a plain `call`.
    fn innermost_pad(&mut self, span: Location) -> Option<BlockIdentity> {
        let depth = self
            .context
            .scopes
            .iter()
            .rposition(|scope| !scope.actions.is_empty())?;
        Some(self.allocate_pad(depth, span))
    }

    /// Allocates the cleanup pad block for the scope at `depth` (memoized on the scope), recursively
    /// allocating the chain of enclosing pads, and records each in `pending_pads` for later filling.
    /// The chained pads, innermost first, drop every live frame local exactly once on the error path
    /// — mirroring the inline unwinding `emit_unwind_drops`/`emit_return_drops` perform for
    /// `break`/`return`, but reached via an `invoke`'s unwind edge.
    fn allocate_pad(&mut self, depth: usize, span: Location) -> BlockIdentity {
        if let Some(pad) = self.context.scopes[depth].pad {
            return pad;
        }
        let pad = self.context.function.add_block().id();
        // Record the pad on its scope before recursing, so the (strictly outward) chain is memoized
        // against re-entry.
        self.context.scopes[depth].pad = Some(pad);

        // The pad of the nearest enclosing scope with obligations, if any.
        let outer = self.context.scopes[..depth]
            .iter()
            .rposition(|scope| !scope.actions.is_empty())
            .map(|outer_depth| self.allocate_pad(outer_depth, span));

        // Capture this scope's actions (reversed: last-declared runs first) while the scope is still
        // live; the body is emitted later by `fill_pending_pads`.
        let actions: Vec<CleanupAction> = self.context.scopes[depth]
            .actions
            .iter()
            .rev()
            .cloned()
            .collect();
        self.context.pending_pads.push(PendingPad {
            block: pad,
            actions,
            outer,
            span,
        });
        pad
    }

    /// Emits the bodies of all deferred cleanup pads, at function finalization. Each pad block is
    /// empty until now, so filling them here — after the body's last block is terminated — keeps every
    /// block a contiguous instruction range. A pad runs its (init-guarded) drops, then `br`s to its
    /// outer pad or `resume`s.
    fn fill_pending_pads(&mut self) {
        let pads = std::mem::take(&mut self.context.pending_pads);
        for pad in pads {
            self.context.point = InsertionPoint::End(pad.block);
            for action in pad.actions {
                self.emit_cleanup(pad.span, action);
            }
            match pad.outer {
                Some(outer_pad) => self.insert(Instruction::br(pad.span, outer_pad)),
                None => self.insert(Instruction::resume(pad.span)),
            };
        }
    }

    /// Emits a call to `callee` whose evaluation carries `effects`. A call that those effects mark
    /// *fallible* (see [`effects_are_fallible`]) and that has an enclosing cleanup pad is lowered as an
    /// `invoke` whose unwind edge runs that pad (dropping the frame's live locals before the error
    /// propagates), with lowering continuing in a fresh continuation block; any other call is a plain
    /// `call`. This is the only place `invoke` is introduced, and the single point at which a call's
    /// fallibility is decided — so no call site can forget to request an unwind edge.
    fn emit_call(
        &mut self,
        span: Location,
        callee: ssa::Value,
        arguments: Vec<ssa::Value>,
        effects: &EffType,
    ) {
        if effects_are_fallible(effects) {
            if let Some(pad) = self.innermost_pad(span) {
                let cont = self.context.function.add_block().id();
                self.insert(Instruction::invoke(span, callee, arguments, cont, pad));
                self.context.point = InsertionPoint::End(cont);
                return;
            }
        }
        self.insert(Instruction::call(span, callee, arguments));
    }

    /// Allocates frame storage for every [`LocalStorage::Owned`] local of the lowered function and
    /// binds it to its `alloca` place.
    ///
    /// Arguments are `NonOwning` and keep their by-value parameter binding. A lowered closure's
    /// captured-environment slots are `Owned` (the body owns the cloned environment) but are *also*
    /// parameters, already bound to their incoming pointers by the parameter loop; they must keep
    /// that binding rather than be re-allocated, so locals already bound (the runtime arguments) are
    /// skipped here. Non-owning, non-argument locals (aliases) are bound to their initializer's place
    /// when their `StoreLocal` is lowered.
    fn allocate_owned_locals(&mut self) {
        let f = self.module.get_function_by_id(self.context.source).unwrap();
        let owned: Vec<(LocalDeclId, Type)> = f
            .locals
            .iter()
            .enumerate()
            .filter(|(i, l)| {
                l.owns_storage()
                    && !self
                        .context
                        .locals
                        .contains_key(&LocalDeclId::from_index(*i))
            })
            .map(|(i, l)| (LocalDeclId::from_index(i), l.ty))
            .collect();
        for (id, ty) in owned {
            let place = self.alloca_storage(self.context.span, ty);
            self.context.locals.insert(id, place);
        }
    }

    /// Returns the `Value` dictionary parameter (a place) witnessing the run-time layout of `ty`, if any.
    fn value_dictionary(&self, ty: Type) -> Option<ssa::Value> {
        self.context
            .value_witnesses
            .iter()
            .find(|(t, _)| *t == ty)
            .map(|(_, w)| w.clone())
    }

    /// Returns whether `ty` has a statically known run-time layout, so that storage for it may be
    /// allocated with a plain `alloca` and a value of that type moved with direct `load`/`store`.
    ///
    /// A `Native` type such as `array<A>` (`[A]`) is statically sized even when generic: its
    /// representation is a fixed-layout struct whose size is independent of its type arguments. Only
    /// a value *of* a bare type variable — or an aggregate embedding one directly — has a layout that
    /// depends on a run-time witness (see [`type_has_static_layout`]).
    fn is_statically_sized(&self, ty: Type) -> bool {
        let env = ModuleEnv::new(self.module, self.others);
        type_has_static_layout(ty, self.context.span, &env)
    }

    /// Inserts an allocation of storage for an instance of `ty` and returns its address.
    ///
    /// Statically sized storage is allocated directly; storage whose size depends on a generic type
    /// variable carries the `Value` dictionary witnessing its run-time layout as operand.
    fn alloca_storage(&mut self, span: Location, ty: Type) -> ssa::Value {
        if self.is_statically_sized(ty) {
            self.insert(Instruction::alloca(span, ty)).unwrap()
        } else {
            let witness = self.value_dictionary(ty).unwrap_or_else(|| {
                panic!(
                    "no Value dictionary witnesses the layout of generic storage of type {}",
                    self.show(ty)
                )
            });
            self.insert(Instruction::alloca_dynamic(span, ty, witness))
                .unwrap()
        }
    }

    /// Asserts that `ty` has a statically known layout, so that a value of that type may be moved
    /// with direct `load`/`store` instructions.
    ///
    /// A value whose size depends on a bare type variable has no static layout: it must be allocated
    /// with `alloca_dynamic` and moved through its `Value` dictionary witness
    /// (`Value::clone`/`Value::drop`), never with direct `load`/`store`.
    fn assert_statically_sized(&self, ty: Type) {
        assert!(
            self.is_statically_sized(ty),
            "attempted direct load/store of a generic value of type {}; generic values must be moved through their Value dictionary witness",
            self.show(ty)
        );
    }

    /// Returns the declaration for `l` within the currently-lowered function.
    fn local_declaration(&self, l: LocalDeclId) -> &module::ELocalDecl {
        &self
            .module
            .get_function_by_id(self.context.source)
            .unwrap()
            .locals[l.as_index()]
    }

    /// Returns the place (a pointer SSA value) backing the local `l`.
    ///
    /// Every local is bound to a place: an incoming by-pointer parameter or an `Owned` `alloca`
    /// or a non-owned alias.
    fn place_of_local(&self, l: LocalDeclId) -> ssa::Value {
        self.context
            .locals
            .get(&l)
            .expect("local must be bound in the current frame")
            .clone()
    }

    /// Lowers an aggregate (tuple or record) into `destination` by projecting each field of the
    /// destination place and lowering the corresponding node into it.
    ///
    /// With no destination the aggregate is built for effects only (e.g. a tuple/record literal in
    /// non-tail statement position): it is materialized into a throwaway temporary so each field's
    /// side effects are still lowered. The temporary's own drop, if any, is emitted by the
    /// enclosing block's cleanup scope.
    fn lower_aggregate_into(
        &mut self,
        node: &ENode,
        fields: &[hir::ENodeId],
        destination: Option<ssa::Value>,
    ) {
        let d = destination.unwrap_or_else(|| self.alloca_storage(node.span, node.ty));
        if fields.is_empty() {
            // A zero-field aggregate (an empty `struct`/record) has no field store to mark its
            // storage live, so the interpreter could not tell a constructed value from
            // uninitialized storage (both have an empty run-time shape) and would skip its
            // `Value::drop`. Store an empty-tuple literal explicitly — mirroring the HIR
            // interpreter's `build record {}`, which yields and stores a live empty aggregate.
            let empty = ssa::Value::Literal(containers::b(LiteralValue::new_tuple(vec![])));
            self.store(node.span, empty, d);
            return;
        }
        for (i, n) in fields.iter().enumerate() {
            let field = &self.hir_arena[*n];
            let f = self
                .insert(Instruction::subfield(
                    field.span,
                    d.clone(),
                    int_constant(i as isize),
                    field.ty,
                ))
                .unwrap();
            self.lower_value_into(field, Some(f));
        }
    }

    /// Lowers an array literal `[e0, e1, …]` into `destination`.
    ///
    /// Mirrors the interpreter's `array_value_from_vec` (`std::array_type`): an `array<A>` is the
    /// record `{ capacity, data, len, start }` whose `data` is a heap `Buffer<A>`. Rather than add
    /// dedicated array IR, the literal is desugared to the same std primitives the `.fer` array
    /// methods use — `buffer_with_capacity` allocates the backing storage, and each element is
    /// lowered in place into the slot place yielded by `buffer_slot` (no temporary, no copy). The
    /// scalar header fields are then stored directly: `capacity = len = N`, `start = 0`.
    fn lower_array_into(
        &mut self,
        node: &ENode,
        ids: &[hir::ENodeId],
        destination: Option<ssa::Value>,
    ) {
        // With no destination the array is built for effects only (e.g. a literal in non-tail
        // statement position): it is materialized into a throwaway temporary so each element's side
        // effects are still lowered. The temporary's own drop, if any, is emitted by the enclosing
        // block's cleanup scope.
        let dest = destination.unwrap_or_else(|| self.alloca_storage(node.span, node.ty));
        let span = node.span;
        let len = ids.len();

        // Resolve the array record's instantiated shape so its fields are addressed by their
        // normalized (name-sorted) positions instead of a hard-coded layout. The named type and
        // the field list are cloned out of their type-universe read guards before any instruction
        // is emitted: interning a new type takes a write lock, which would deadlock against a still
        // held read guard.
        let named = node
            .ty
            .data()
            .as_named()
            .cloned()
            .expect("an array literal must have a named array type");
        let element_ty = named.params[0];
        let shape = named.instantiated_shape(&ModuleEnv::new(self.module, self.others));
        let fields = shape
            .data()
            .as_record()
            .cloned()
            .expect("the array shape must be a record");
        let field = |name: &str| {
            fields
                .iter()
                .position(|(n, _)| n.as_str() == name)
                .unwrap_or_else(|| panic!("the array record has no `{name}` field"))
        };
        let capacity_index = field("capacity");
        let data_index = field("data");
        let len_index = field("len");
        let start_index = field("start");

        // Allocate the backing buffer straight into the record's `data` field, i.e.
        // `data = buffer_with_capacity(N)` (the returned `Buffer<A>` is written through the call's
        // out-pointer).
        let data_place = self
            .insert(Instruction::subfield(
                span,
                dest.clone(),
                int_constant(data_index as isize),
                fields[data_index].1,
            ))
            .unwrap();
        let with_capacity = ssa::Value::Function(self.demand_std_function("buffer_with_capacity"));
        let capacity_arg = self.int_constant_place(span, len as isize);
        self.insert(Instruction::call(
            span,
            with_capacity,
            [capacity_arg, data_place.clone()],
        ));

        // Fill each slot in place: `buffer_slot(data, i)` yields the slot's place (an
        // `AddressorPlace` return), into which element `i` is lowered directly.
        if len > 0 {
            let buffer_slot = ssa::Value::Function(self.demand_std_function("buffer_slot"));
            for (i, id) in ids.iter().enumerate() {
                let index_arg = self.int_constant_place(span, i as isize);
                let slot_out = self
                    .insert(Instruction::alloca_place(span, element_ty))
                    .unwrap();
                self.insert(Instruction::call(
                    span,
                    buffer_slot.clone(),
                    [data_place.clone(), index_arg, slot_out.clone()],
                ));
                let slot = self.insert(Instruction::load(span, slot_out)).unwrap();
                self.lower_value_into(&self.hir_arena[*id], Some(slot));
            }
        }

        // Store the scalar header fields: a freshly built array is contiguous and full, so
        // `capacity == len == N` and `start == 0`.
        self.store_int_field(
            span,
            &dest,
            capacity_index,
            fields[capacity_index].1,
            len as isize,
        );
        self.store_int_field(span, &dest, len_index, fields[len_index].1, len as isize);
        self.store_int_field(span, &dest, start_index, fields[start_index].1, 0);
    }

    /// Returns the `FunctionReference` of the std-library function named `name`. Used to synthesize
    /// calls to std primitives (e.g. the `buffer_*` intrinsics) that the lowered source need not
    /// itself import.
    fn demand_std_function(&self, name: &str) -> FunctionReference {
        let std_module = self.session.expect_fresh_module(STD_MODULE_ID);
        let id = std_module
            .get_local_function_id(Ustr::from(name))
            .unwrap_or_else(|| panic!("std function `{name}` not found"));
        self.demand_function(id, STD_MODULE_ID)
    }

    /// Allocates a fresh `int` slot, stores the constant `value` into it, and returns its place.
    /// Used to materialize the by-pointer integer arguments of synthesized `buffer_*` calls.
    fn int_constant_place(&mut self, span: Location, value: isize) -> ssa::Value {
        let place = self
            .insert(Instruction::alloca(span, crate::std::math::int_type()))
            .unwrap();
        self.insert(Instruction::store(span, int_constant(value), place.clone()));
        place
    }

    /// Stores the integer constant `value` into the `index`-th field (of type `ty`) of the record
    /// at `dest`.
    fn store_int_field(
        &mut self,
        span: Location,
        dest: &ssa::Value,
        index: usize,
        ty: Type,
        value: isize,
    ) {
        let place = self
            .insert(Instruction::subfield(
                span,
                dest.clone(),
                int_constant(index as isize),
                ty,
            ))
            .unwrap();
        self.insert(Instruction::store(span, int_constant(value), place));
    }

    /// Returns whether lowering `node` as a place yields an existing (aliased) place rather than
    /// materializing the value into a fresh temporary.
    ///
    /// This mirrors the place-producing arms of [`lower_as_place`](Self::lower_as_place): locals,
    /// dictionaries, projections, and `with`-place bindings are always places; a call is a place
    /// only when it returns one (`returns_place`); a block forwards to its tail. It is used to
    /// decide whether a block in place position must forward to its tail's place (to preserve place
    /// identity) instead of being materialized into a temporary.
    fn node_yields_place(&self, node: &ENode) -> bool {
        use hir::NodeKind as K;
        match &node.kind {
            K::LoadLocal(_)
            | K::LoadDictionary(_)
            | K::LoadFieldIndex(_)
            | K::Project(_)
            | K::ProjectAt(_)
            | K::GetDictionaryMethod(_)
            | K::WithPlace(_) => true,
            K::Apply(n) => n.ty.returns_place(),
            K::StaticApply(n) => n.ty.returns_place(),
            K::CallDictionaryMethod(n) => n.ty.returns_place(),
            K::Block(n) => n
                .body
                .last()
                .is_some_and(|t| self.node_yields_place(&self.hir_arena[*t])),
            _ => false,
        }
    }

    /// Lowers `node` as a place.
    ///
    /// If possible, lowers directly as a place, otherwise lowers a value into stack storage,
    /// returning its address.
    fn lower_as_place(&mut self, node: &ENode) -> ssa::Value {
        use hir::NodeKind as K;
        match &node.kind {
            K::LoadLocal(n) => self.place_of_local(n.id),

            K::LoadDictionary(n) => {
                // A dictionary parameter is already a place.
                self.context.extra_parameters[&n.extra_parameter].clone()
            }

            K::LoadFieldIndex(n) => {
                // A field-index parameter (an `int` passed by pointer) is already a place, forwarded
                // unchanged as the dictionary argument of a downstream generic-record access.
                self.context.extra_parameters[&n.extra_parameter].clone()
            }

            K::Project(n) => {
                let base_node = &self.hir_arena[n.value];
                // A projection whose base is a dictionary extracts a dictionary entry (a method or
                // associated const — `TraitDictionaryEntry` has no nested-dictionary variant, so a
                // dictionary base is always a `GetDictionary`/`LoadDictionary` node). It lowers to
                // the symbolic `dict_entry`, not a tuple `project`: a forwarded dictionary is an
                // interned id, not a place to index into. A non-dictionary base (a tuple/record
                // place) keeps the ordinary `project`.
                if matches!(
                    base_node.kind,
                    hir::NodeKind::GetDictionary(_) | hir::NodeKind::LoadDictionary(_)
                ) {
                    let dict = self.lower_dictionary_operand(base_node);
                    self.insert(Instruction::dict_entry(
                        node.span,
                        dict,
                        n.index.as_index(),
                        node.ty,
                    ))
                    .unwrap()
                } else {
                    let base = self.lower_as_place(base_node);
                    self.insert(Instruction::subfield(
                        node.span,
                        base,
                        int_constant(n.index.as_index() as isize),
                        node.ty,
                    ))
                    .unwrap()
                }
            }

            K::ProjectAt(n) => {
                // A field access on a generic (row-polymorphic) record: project the base place at
                // the run-time field offset held in the field-index dictionary parameter `n.index`.
                // That parameter is a place (a pointer to an `int`); load it to get the index, then
                // project. Mirrors the HIR interpreter's `eval_project_at`, which pushes the loaded
                // index onto the base place's path - no temporary, so the (possibly generic) field
                // type needs no `Value` layout witness.
                let base = self.lower_as_place(&self.hir_arena[n.value]);
                let index_param = self.context.extra_parameters[&n.index].clone();
                let index = self
                    .insert(Instruction::load(node.span, index_param))
                    .unwrap();
                self.insert(Instruction::subfield(node.span, base, index, node.ty))
                    .unwrap()
            }

            K::Apply(n) => {
                let result_storage = self.allocate_result(node, &n.ty);
                // The callee is lowered as a *place*: a function value (in particular a closure) is
                // borrowed in place and read by reference at the call, so it survives repeated calls
                // (`f() + f()`) and is dropped once by its scope cleanup — mirroring the HIR
                // interpreter's `eval_apply`, which calls through a borrow of the function value.
                let f = self.lower_as_place(&self.hir_arena[n.function]);
                let mut arguments: Vec<ssa::Value> = n
                    .arguments
                    .iter()
                    .map(|arg| self.lower_argument(arg))
                    .collect();
                arguments.push(result_storage.clone());

                self.emit_call(node.span, f, arguments, &node.effects);

                if n.ty.returns_place() {
                    self.insert(Instruction::load(node.span, result_storage))
                        .unwrap()
                } else {
                    result_storage
                }
            }

            K::StaticApply(n) => {
                let (fi, mi) = self.resolve_function(n.function);
                let f = ssa::Value::Function(self.demand_function(fi, mi));
                let mut arguments: Vec<ssa::Value> = vec![];
                for x in &n.extra_arguments {
                    arguments.push(self.lower_extra_argument(&self.hir_arena[*x]));
                }
                for arg in &n.arguments {
                    arguments.push(self.lower_as_place(&self.hir_arena[arg.value]));
                }

                let result_storage = self.allocate_result(node, &n.ty);
                arguments.push(result_storage.clone());

                self.emit_call(node.span, f, arguments, &node.effects);

                if n.ty.returns_place() {
                    self.insert(Instruction::load(node.span, result_storage))
                        .unwrap()
                } else {
                    result_storage
                }
            }

            K::CallDictionaryMethod(n) => {
                // A place-returning method dispatched through a dictionary: project+load the
                // method, call it with a place out-pointer, then load the returned place.
                let (method, mut arguments) = self.lower_dictionary_method_target(node, n);
                let result_storage = self.allocate_result(node, &n.ty);
                arguments.push(result_storage.clone());
                self.emit_call(node.span, method, arguments, &node.effects);
                if n.ty.returns_place() {
                    self.insert(Instruction::load(node.span, result_storage))
                        .unwrap()
                } else {
                    result_storage
                }
            }

            K::GetDictionaryMethod(n) => {
                // A trait method taken as a first-class value through a (generic) dictionary: the
                // symbolic analog of projecting the method out of the witness table. `dict_entry`
                // yields the place of the method's (bare) function value, which the consumer reads
                // by reference at the call — exactly like a `project`ed method slot.
                let dictionary = self.lower_dictionary_operand(&self.hir_arena[n.dictionary]);
                self.insert(Instruction::dict_entry(
                    node.span,
                    dictionary,
                    n.entry_index.as_index(),
                    node.ty,
                ))
                .unwrap()
            }

            K::WithPlace(n) => {
                // An addressor subscript site: bind the accessor's place, then the body (a
                // `LoadLocal` of the binding, possibly projected) is itself a place.
                self.bind_local_for_with_place(n);
                self.lower_as_place(&self.hir_arena[n.body])
            }

            K::Block(n) if self.node_yields_place(node) => {
                // A block in place position whose tail is itself a place (e.g., an addressor body
                // ending in `return effects_unsafe { buffer_slot(..) }`) is *that* place: open the
                // block's scope, lower the leading statements for their effects, then alias the
                // tail's place. Forwarding to the tail rather than materializing the block into a
                // temporary preserves place identity (the addressor must yield the real slot, not a
                // copy) and avoids allocating storage for a generic block type, which has no `Value`
                // layout witness. A value-tailed block does not match this guard and falls through
                // to the default arm, which materializes it into a temporary as before.
                let cleanup = n.cleanup.clone();
                self.enter_scope(&cleanup);
                let (tail, init) = n
                    .body
                    .split_last()
                    .expect("node_yields_place implies a non-empty block body");
                for s in init {
                    if self.current_block_is_terminated() {
                        break;
                    }
                    self.lower_value_into(&self.hir_arena[*s], None);
                }
                let place = if self.current_block_is_terminated() {
                    // Dead code: a leading statement terminated the block, so the tail place is
                    // unreachable. Return an arbitrary valid place (the return out-pointer) that is
                    // never consumed.
                    self.context.return_destination.clone()
                } else {
                    self.lower_as_place(&self.hir_arena[*tail])
                };
                self.exit_scope(node.span);
                place
            }

            // A value-producing node — including a `WithYielded`, whose result is a *copy* of the
            // yielded value taken while the accessor is suspended, not the (transient) yielded place
            // itself — is materialized into a temporary place.
            _ => {
                let storage = self.alloca_storage(node.span, node.ty);
                self.lower_value_into(node, Some(storage.clone()));
                storage
            }
        }
    }

    /// Lowers the *enter* half of a [`hir::WithYielded`]: runs the accessor (a `StaticApply` of the
    /// `YieldedOnce` member) to its `yield` with a `project`, binds the non-owning `binding` local to
    /// the exposed place, and opens the dedicated scope whose `end_project` runs the accessor slide on
    /// exit. The caller then lowers `n.body` and `exit_scope`s. Mirrors `eval_with_yielded`.
    fn lower_with_yielded_enter(&mut self, n: &hir::WithYielded<Elaborated>) {
        let accessor = &self.hir_arena[n.accessor];
        let app = match &accessor.kind {
            hir::NodeKind::StaticApply(app) => app,
            other => panic!(
                "a WithYielded accessor must be a StaticApply of a YieldedOnce member, got {other:?}"
            ),
        };
        let (fi, mi) = self.resolve_function(app.function);
        let callee = ssa::Value::Function(self.demand_function(fi, mi));
        let mut arguments: Vec<ssa::Value> = vec![];
        for x in &app.extra_arguments {
            arguments.push(self.lower_extra_argument(&self.hir_arena[*x]));
        }
        for arg in &app.arguments {
            arguments.push(self.lower_as_place(&self.hir_arena[arg.value]));
        }
        // The exposed place's pointee type is the binding's (element) type. `project` runs the ramp
        // to the yield and binds the yielded place to its result register.
        //
        // NOTE: the ramp is lowered as a plain `project` even when fallible; a ramp raise propagates
        // straight out without running the caller's cleanup pad. The current `let`/`inout` accessors
        // have infallible ramps, so this is not yet exercised; a fallible-ramp accessor would need an
        // `invoke`-style `project` (a follow-up), the same way `emit_call` chooses `invoke`.
        let element_ty = self.local_declaration(n.binding).ty;
        let place = self
            .insert(Instruction::project(
                accessor.span,
                callee,
                arguments,
                element_ty,
            ))
            .unwrap();
        self.context.locals.insert(n.binding, place.clone());
        self.enter_projection_scope(place);
    }

    /// Lowers the addressor `place` of a [`hir::WithPlace`] and binds its non-owning `binding`
    /// local to that place, so the driver `body` can read it through `LoadLocal(binding)`.
    ///
    /// Mirrors the interpreter's `eval_with_place`: the binding aliases existing caller-rooted
    /// storage, so no store is emitted (the same shape as a non-owning `StoreLocal` alias).
    fn bind_local_for_with_place(&mut self, n: &hir::WithPlace<Elaborated>) {
        let place = self.lower_as_place(&self.hir_arena[n.place]);
        self.context.locals.insert(n.binding, place);
    }

    /// Lowers a `Case` scrutinee to an operand `comp_eq` reads *non-consumingly*.
    ///
    /// An immediate scalar stays a primitive constant; everything else is taken as its **place** (a
    /// borrow), never loaded/moved. This mirrors the HIR interpreter's `eval_case`, which reads the
    /// scrutinee through `target_ref` and compares its `to_literal_value()`: the place stays live for
    /// the remaining alternatives and for the arm body (so a non-trivial scrutinee — string/tuple —
    /// is not consumed), and a bare-generic scrutinee needs no static-layout assertion because it is
    /// only borrowed and snapshotted, not loaded as a register. (A variant scrutinee arrives as the
    /// `int` `extract_tag`, materialized into a place here.)
    fn lower_case_scrutinee(&mut self, node: &ENode) -> ssa::Value {
        use hir::NodeKind as K;
        if let K::Immediate(n) = &node.kind
            && let Some(prim) = self.lower_as_primitive(n)
        {
            return prim;
        }
        self.lower_as_place(node)
    }

    /// Lowers a `Case` pattern to an operand for `comp_eq`. A scalar pattern uses its primitive form;
    /// a composite (tuple/record) pattern — which has no single scalar form — is carried whole as an
    /// [`ssa::Value::Literal`], so `comp_eq` compares the whole scrutinee against the whole pattern
    /// structurally, exactly as the HIR interpreter's `eval_case` compares `LiteralValue`s.
    fn lower_case_pattern(&mut self, pattern: &LiteralValue) -> ssa::Value {
        self.lower_as_primitive(pattern)
            .unwrap_or_else(|| ssa::Value::Literal(containers::b(pattern.clone())))
    }

    /// Lowers `arg` to its call operand: a pointer to the argument's storage.
    ///
    /// Note: All arguments are passed indirectly in SSA IR.
    fn lower_argument(&mut self, arg: &CallArgument<Elaborated>) -> ssa::Value {
        self.lower_as_place(&self.hir_arena[arg.value])
    }

    /// Returns the blocks created for `n`.
    fn create_case_blocks(&mut self, n: &Case<Elaborated>) -> CaseBlocks {
        let mut heads: Vec<BlockIdentity> = vec![];
        let mut bodies: Vec<BlockIdentity> = vec![];
        for _ in n.alternatives.iter() {
            heads.push(self.context.function.add_block().id());
            bodies.push(self.context.function.add_block().id());
        }
        let default: BlockIdentity = self.context.function.add_block().id();
        let tail: BlockIdentity = self.context.function.add_block().id();
        CaseBlocks {
            heads,
            bodies,
            default,
            tail,
        }
    }

    /// Returns the symbolic SSA dictionary lowered from `n`: the canonical interned handle of the
    /// impl that satisfies it. The dictionary is kept symbolic (not materialized into a witness-table
    /// tuple); the SSA interpreter dispatches through it via `DictArg::Interned`, and a future
    /// tuple-lowering pass rebuilds the table from the impl arena.
    fn lower_dictionary(&mut self, n: &GetDictionary) -> ssa::Value {
        ssa::Value::Dictionary(self.dictionary_id(n.dictionary))
    }

    /// Lowers a HIR dictionary node to a symbolic SSA dictionary operand.
    ///
    /// A static `GetDictionary` becomes a `Dictionary(id)` constant; a forwarded `LoadDictionary`
    /// becomes the `@extra` parameter slot it arrives in (a `Parameter`). The dictionary is never
    /// materialized into a witness-table tuple. (Dictionary entries are only methods and associated
    /// consts — `TraitDictionaryEntry` has no nested-dictionary variant — so a dictionary operand is
    /// always one of these two node kinds.)
    fn lower_dictionary_operand(&self, node: &ENode) -> ssa::Value {
        use hir::NodeKind as K;
        match &node.kind {
            K::GetDictionary(d) => ssa::Value::Dictionary(self.dictionary_id(d.dictionary)),
            K::LoadDictionary(n) => self.context.extra_parameters[&n.extra_parameter].clone(),
            other => panic!("expected a trait dictionary node, got {:?}", other),
        }
    }

    /// Lowers a call's extra (evidence) argument to its SSA operand: a trait dictionary becomes a
    /// symbolic dictionary operand (`lower_dictionary_operand`), while field-index evidence (an
    /// `int`, from `LoadFieldIndex` or an `Immediate`) is lowered as a place as before.
    fn lower_extra_argument(&mut self, node: &ENode) -> ssa::Value {
        use hir::NodeKind as K;
        match &node.kind {
            K::GetDictionary(_) | K::LoadDictionary(_) => self.lower_dictionary_operand(node),
            _ => self.lower_as_place(node),
        }
    }

    /// Stores the register `value` into `dest` if a destination is present; a `None` `dest`
    /// discards the value.
    fn store_into_if_needed(
        &mut self,
        span: Location,
        value: ssa::Value,
        destination: Option<ssa::Value>,
    ) {
        if let Some(d) = destination {
            self.insert(Instruction::store(span, value, d));
        }
    }

    /// Inserts a `store` instruction to store `v` at `destination`.
    fn store(&mut self, span: Location, v: ssa::Value, destination: ssa::Value) {
        self.insert(Instruction::store(span, v, destination));
    }

    /// Copies the pointee of the place `source` into `destination` as a single `memcpy` (the fused
    /// form of a `load` immediately followed by a `store` of the loaded value). A `None`
    /// `destination` discards the copy.
    fn memcpy_into_if_needed(
        &mut self,
        span: Location,
        source: ssa::Value,
        destination: Option<ssa::Value>,
    ) {
        if let Some(d) = destination {
            self.insert(Instruction::memcpy(span, source, d));
        }
    }

    /// Moves the whole pointee of `source` into `destination`, choosing a plain `memcpy` for a
    /// statically-sized value or a witnessed `memcpy_dynamic` for a generic (dynamically-sized) one.
    ///
    /// Unlike a *copy*, a move transfers ownership wholesale and needs no `Value::clone`; a generic
    /// move is therefore a byte-move whose size the witness supplies (the interpreter moves the value
    /// shape-agnostically and ignores the witness).
    fn move_value_into(
        &mut self,
        span: Location,
        source: ssa::Value,
        destination: ssa::Value,
        ty: Type,
    ) {
        if self.is_statically_sized(ty) {
            self.insert(Instruction::memcpy(span, source, destination));
        } else {
            let witness = self.value_dictionary(ty).unwrap_or_else(|| {
                panic!(
                    "no Value dictionary witnesses the layout of the generic value of type {} moved out",
                    self.show(ty)
                )
            });
            self.insert(Instruction::memcpy_dynamic(
                span,
                source,
                destination,
                witness,
            ));
        }
    }

    /// Projects the method function reference out of `n`'s dictionary place, loads it, and lowers
    /// the call's runtime arguments to their place operands. Returns `(method, arguments)` ready
    /// to be completed with a result out-pointer and emitted as a `call`.
    fn lower_dictionary_method_target(
        &mut self,
        node: &ENode,
        n: &hir::CallDictionaryMethod<Elaborated>,
    ) -> (ssa::Value, Vec<ssa::Value>) {
        let dictionary = self.lower_dictionary_operand(&self.hir_arena[n.dictionary]);
        let method_ty = Type::function_type(n.ty.clone());
        // The callee is the place of the method entry; the call reads the function value by
        // reference rather than loading it into a register (see the `call` contract).
        let method_place = self
            .insert(Instruction::dict_entry(
                node.span,
                dictionary,
                n.entry_index.as_index(),
                method_ty,
            ))
            .unwrap();
        let arguments = n.arguments.iter().map(|a| self.lower_argument(a)).collect();
        (method_place, arguments)
    }

    /// Inserts an allocation of the result storage for a call to a function of type `f` and returns
    /// its address. `node` supplies the span and the concrete result type for the allocation.
    ///
    /// The allocation depends on `f`'s return convention:
    /// - [`FnReturnConvention::Value`] allocates storage for the returned value (`alloca`) — including
    ///   a unit return, which allocates a (zero-sized) `()` cell the callee initializes with the live
    ///   unit value, so every result, unit or not, flows through a real cell;
    /// - [`FnReturnConvention::AddressorPlace`] allocates a slot holding the returned place pointer
    ///   (`alloca_place`).
    ///
    /// [`FnReturnConvention::YieldedOnce`] is never reached here: a yielded member is entered with a
    /// `project` (which exposes the yielded place as its own result register), never called for a
    /// result through this helper.
    fn allocate_result(&mut self, node: &ENode, f: &FnType) -> ssa::Value {
        match f.return_convention {
            FnReturnConvention::Value => self.alloca_storage(node.span, node.ty),
            FnReturnConvention::AddressorPlace => self
                .insert(Instruction::alloca_place(node.span, node.ty))
                .unwrap(),
            FnReturnConvention::YieldedOnce => {
                panic!("a YieldedOnce member is entered via `project`, never called for a result")
            }
        }
    }

    /// Lowers a place-returning call in value position: the call's place result is resolved and
    /// its value is copied into the destination (trivial copy; non-trivial reads are wrapped in
    /// `CloneValue` by HIR). A `None` destination lowers the call for its effects only.
    fn lower_place_call_into(&mut self, node: &ENode, destination: Option<ssa::Value>) {
        let place = self.lower_as_place(node);
        if destination.is_some() {
            self.assert_statically_sized(node.ty);
            self.memcpy_into_if_needed(node.span, place, destination);
        }
    }

    /// Lowers `node` in destination-passing style: the value produced by `node` is stored into the
    /// storage pointed to by `dest`. A `None` `dest` denotes a discarded result (effects only); a
    /// `()`-typed node also has nothing to store.
    fn lower_value_into(&mut self, node: &ENode, destination: Option<ssa::Value>) {
        use hir::NodeKind as K;
        match &node.kind {
            K::Block(n) => {
                // Open a lexical scope holding this block's drop obligations, lower each statement
                // for its effects (the block's value is its tail node, lowered into the
                // destination), then drop the scope's owned locals on the way out. A local moved
                // into the destination (e.g. returned) has been left uninitialized, so its
                // init-guarded `drop` is skipped at run time.
                let cleanup = n.cleanup.clone();
                self.enter_scope(&cleanup);
                if let Some((tail, init)) = n.body.split_last() {
                    for s in init {
                        // A `break`/`continue`/`return` statement terminates the block; any
                        // following statements are unreachable and must not be emitted after a
                        // terminator.
                        if self.current_block_is_terminated() {
                            break;
                        }
                        self.lower_value_into(&self.hir_arena[*s], None);
                    }
                    if !self.current_block_is_terminated() {
                        self.lower_value_into(&self.hir_arena[*tail], destination);
                    }
                }
                self.exit_scope(node.span);
            }

            K::Case(n) => {
                let blocks = self.create_case_blocks(n);

                // Mirror the HIR interpreter's `eval_case`: read the scrutinee once and compare its
                // whole value against each whole pattern (`comp_eq` does `LiteralValue` equality,
                // non-consuming). The scrutinee is taken as a borrowable place — never loaded/moved —
                // so a string/tuple stays live across alternatives and into the arm body; an
                // immediate scrutinee stays a primitive constant. Variant matches arrive here as a
                // match on the (int) `extract_tag` of the scrutinee, so no variant-specific path is
                // needed. (We do *not* decompose composite patterns: the HIR compares the whole tuple
                // structurally, so the SSA does the same.)
                let scrutinee = self.lower_case_scrutinee(&self.hir_arena[n.value]);

                // With no alternatives (e.g. a single irrefutable arm), there are no condition
                // heads to test, so branch straight to the default block.
                let entry = blocks.heads.first().copied().unwrap_or(blocks.default);
                self.insert(Instruction::br(node.span, entry));

                // Lower the alternatives. Each alternative stores its value directly into `dest`.
                for (i, (c, a)) in n.alternatives.iter().enumerate() {
                    // Load the next alternative's condition if there's one. Otherwise, we've reached the
                    // default case.
                    let next = if i < n.alternatives.len() - 1 {
                        blocks.heads[i + 1]
                    } else {
                        blocks.default
                    };

                    // Transfer control flow to the head of the match. Compare the whole scrutinee
                    // against this alternative's whole pattern and branch to its body on a match or to
                    // `next` otherwise.
                    self.context.point = InsertionPoint::End(blocks.heads[i]);
                    let pattern = self.lower_case_pattern(c);
                    let eq = self
                        .insert(Instruction::compare_eq(
                            node.span,
                            scrutinee.clone(),
                            pattern,
                        ))
                        .unwrap();
                    self.insert(Instruction::condbr(node.span, eq, blocks.bodies[i], next));

                    // Lower the body of the alternative into the destination. A `break`/`continue`/
                    // `return` arm terminates its own block, so it needs no branch to the tail.
                    self.context.point = InsertionPoint::End(blocks.bodies[i]);
                    self.lower_value_into(&self.hir_arena[*a], destination.clone());
                    if !self.current_block_is_terminated() {
                        self.insert(Instruction::br(node.span, blocks.tail));
                    }
                }

                // Default case.
                self.context.point = InsertionPoint::End(blocks.default);
                self.lower_value_into(&self.hir_arena[n.default], destination.clone());
                if !self.current_block_is_terminated() {
                    self.insert(Instruction::br(node.span, blocks.tail));
                }

                // Tail. The value has already been stored into `dest`.
                self.context.point = InsertionPoint::End(blocks.tail);
            }

            K::Immediate(n) => {
                // A unit immediate lowers to `ssa::Value::Unit` like any other primitive: it stores
                // a live `()` into a real destination slot (a no-op into the phantom unit place), so a
                // unit *leaf* of an aggregate — e.g. the `((),)` payload of `Continue(())` — is never
                // left uninitialized.
                if let Some(value) = self.lower_as_primitive(n) {
                    self.store_into_if_needed(node.span, value, destination);
                } else {
                    let s = self.show(node.ty);
                    panic!(
                        "lowering is unimplemented for node of kind '{:?}' of type {:?}",
                        node.kind, s
                    )
                }
            }

            K::Assign(n) => {
                // Mirror the interpreter's `eval_assign` ordering: evaluate the right-hand side,
                // then drop the destination's previous value, then store the new one.
                //
                // The right-hand side may read the destination it overwrites (e.g. `a = a / 2`), so
                // when the old value needs a non-trivial drop we evaluate the new value into a fresh
                // temporary *before* dropping. Dropping first would leave the destination
                // uninitialized and the right-hand side would then read uninitialized storage. With
                // no drop the new value is computed directly into the destination: a call reads its
                // operands before writing its result, so an in-place `f(a, …) -> a` is sound.
                let place = self.lower_as_place(&self.hir_arena[n.place]);
                if let Some(spec) = n.drop.and_then(|d| self.resolve_drop(d)) {
                    let dropped_ty = self.hir_arena[n.place].ty;
                    let value_span = self.hir_arena[n.value].span;
                    let value_ty = self.hir_arena[n.value].ty;
                    let temp = self.alloca_storage(value_span, value_ty);
                    self.lower_value_into(&self.hir_arena[n.value], Some(temp.clone()));
                    self.emit_drop(node.span, place.clone(), dropped_ty, spec);
                    // The fresh temporary is *moved* into the destination (it is consumed, not read
                    // again). A move is shape-agnostic, so it works for a generic `value_ty` too —
                    // `move_value_into` carries the run-time-layout witness via `memcpy_dynamic` when
                    // the type is not statically sized, unlike a bare `memcpy` (which requires a known
                    // layout — see `Instruction::memcpy`).
                    self.move_value_into(node.span, temp, place, value_ty);
                } else {
                    self.lower_value_into(&self.hir_arena[n.value], Some(place));
                }
                // `Assign` is `()`-typed: nothing to store into `dest`.
            }

            K::LoadLocal(n) => {
                // A bare load in value position is a trivial-copy read (non-trivial reads are wrapped
                // in `CloneValue`/`TakeLocalValue` by HIR): copy the local's place into the dest.
                if destination.is_some() {
                    self.assert_statically_sized(node.ty);
                    let p = self.place_of_local(n.id);
                    self.memcpy_into_if_needed(node.span, p, destination);
                }
            }

            K::StoreLocal(n) => {
                // Initialize the local's storage. A non-owning local is an alias: bind it to the
                // place of its initializer (no store). Otherwise the local's `clone` dispatch
                // decides how the value is produced: `None`/`TrivialCopy` stores the produced
                // value directly; `Static`/`Dictionary` perform `Value::clone` into the target
                // (deferred).
                if !self.local_declaration(n.id).owns_storage() {
                    let aliasee = self.lower_as_place(&self.hir_arena[n.value]);
                    self.context.locals.insert(n.id, aliasee);
                    return;
                }
                let clone = self.local_declaration(n.id).clone;
                match clone {
                    None | Some(ResolvedLocalClone::TrivialCopy) => {
                        let place = self.place_of_local(n.id);
                        self.lower_value_into(&self.hir_arena[n.value], Some(place));
                    }
                    Some(ResolvedLocalClone::Static(f)) => {
                        // Clone the source place into the local's (uninitialized) owned storage
                        // through the statically known clone function `f`.
                        let (fi, mi) = self.resolve_function(f);
                        let f = ssa::Value::Function(self.demand_function(fi, mi));

                        let target = self.place_of_local(n.id);
                        let source = self.lower_as_place(&self.hir_arena[n.value]);

                        // A plain `call`, not an `invoke`: `Value::clone` is declared with an empty
                        // effect row (a fallible clone impl is a compile error —
                        // `TraitMethodEffectMismatch`), so the clone can never raise and needs no
                        // cleanup-pad unwind edge.
                        self.insert(Instruction::call(node.span, f, [source, target]));
                    }
                    Some(ResolvedLocalClone::Dictionary(dictionary)) => {
                        // Clone the source place into the local's (uninitialized) owned storage
                        // through the `Value::clone` method loaded from the dictionary parameter.
                        let cloned_ty = self.local_declaration(n.id).ty;
                        let target = self.place_of_local(n.id);
                        let source = self.lower_as_place(&self.hir_arena[n.value]);
                        self.lower_value_clone_via_dictionary(
                            node.span, dictionary, cloned_ty, source, target,
                        );
                    }
                }
                // `StoreLocal` is `()`-typed: nothing to store into `dest`.
            }

            K::CloneValue(n) => {
                match n.clone {
                    // A trivial copy: load the source place and store it into the destination. A later
                    // ABI pass may relax this to direct passing where physically possible.
                    ResolvedLocalClone::TrivialCopy => {
                        self.lower_value_into(&self.hir_arena[n.source], destination);
                    }
                    ResolvedLocalClone::Static(f) => {
                        // Clone the source place into the local's (uninitialized) owned storage
                        // through the statically known clone function `f`.
                        let (fi, mi) = self.resolve_function(f);
                        let f = ssa::Value::Function(self.demand_function(fi, mi));

                        let source = self.lower_as_place(&self.hir_arena[n.source]);

                        // A plain `call`: `Value::clone` is infallible by its trait contract (see the
                        // `StoreLocal` clone above), so no unwind edge is needed.
                        self.insert(Instruction::call(
                            node.span,
                            f,
                            [source, destination.unwrap()],
                        ));
                    }
                    ResolvedLocalClone::Dictionary(dictionary) => {
                        // Materialize an owned snapshot by cloning the source place into a fresh
                        // target through the `Value::clone` method loaded from the dictionary
                        // parameter. A `None` destination still needs target storage to clone into.
                        let target =
                            destination.unwrap_or_else(|| self.alloca_storage(node.span, node.ty));
                        let source = self.lower_as_place(&self.hir_arena[n.source]);
                        self.lower_value_clone_via_dictionary(
                            node.span, dictionary, node.ty, source, target,
                        );
                    }
                }
            }

            K::TakeLocalValue(n) => match n.mode {
                ResolvedTakeLocalValueMode::MoveOwned => {
                    // Move the owned value out: copy the place into the destination, skipping the
                    // local's lexical drop (cleanup is deferred). A move transfers the value
                    // wholesale, so a generic (dynamically-sized) value needs no `Value::clone` —
                    // just a witnessed dynamic memcpy; a statically-sized one uses a plain memcpy.
                    if let Some(destination) = destination {
                        let source = self.place_of_local(n.id);
                        self.move_value_into(node.span, source, destination, node.ty);
                    }
                }
                ResolvedTakeLocalValueMode::CloneBorrowed(clone) => {
                    // Take a non-owning alias by cloning (or copying) its borrowed value into the
                    // destination, leaving the aliased storage intact. Mirrors `CloneValue`, but the
                    // source is the local's place. A `None` destination discards the result, so the
                    // clone (a pure `Value::clone`) is elided.
                    if let Some(destination) = destination {
                        match clone {
                            ResolvedLocalClone::TrivialCopy => {
                                self.assert_statically_sized(node.ty);
                                let source = self.place_of_local(n.id);
                                self.memcpy_into_if_needed(node.span, source, Some(destination));
                            }
                            ResolvedLocalClone::Static(f) => {
                                let (fi, mi) = self.resolve_function(f);
                                let f = ssa::Value::Function(self.demand_function(fi, mi));
                                let source = self.place_of_local(n.id);
                                // Plain `call`: `Value::clone` is infallible by its trait contract.
                                self.insert(Instruction::call(node.span, f, [source, destination]));
                            }
                            ResolvedLocalClone::Dictionary(dictionary) => {
                                let source = self.place_of_local(n.id);
                                self.lower_value_clone_via_dictionary(
                                    node.span,
                                    dictionary,
                                    node.ty,
                                    source,
                                    destination,
                                );
                            }
                        }
                    }
                }
            },

            K::StaticApply(n) => {
                if n.ty.returns_place() {
                    return self.lower_place_call_into(node, destination);
                }
                let (fi, mi) = self.resolve_function(n.function);
                let f = ssa::Value::Function(self.demand_function(fi, mi));
                let mut arguments: Vec<ssa::Value> = vec![];
                for x in &n.extra_arguments {
                    arguments.push(self.lower_extra_argument(&self.hir_arena[*x]));
                }
                for arg in &n.arguments {
                    arguments.push(self.lower_argument(arg));
                }

                assert_eq!(node.ty, n.ty.ret);
                arguments.push(destination.unwrap_or_else(|| self.allocate_result(node, &n.ty)));
                self.emit_call(node.span, f, arguments, &node.effects);
            }

            K::GetDictionary(d) => {
                let dict = self.lower_dictionary(d);
                self.store_into_if_needed(node.span, dict, destination);
            }

            K::GetFunction(n) => {
                // A first-class reference to a (non-generic) function: lower to a constant function
                // value and store it into the destination. A generic function used first-class is
                // wrapped by elaboration in a `BuildClosure` carrying its dictionary captures, so a
                // bare `GetFunction` never needs evidence here.
                let (fi, mi) = self.resolve_function(n.function);
                let f = ssa::Value::Function(self.demand_function(fi, mi));
                self.store_into_if_needed(node.span, f, destination);
            }

            K::BuildClosure(n) => {
                // Build a first-class closure value bundling the target function with its captured
                // environment. The target's body receives, as leading by-pointer parameters, first
                // its hidden `@extra` dictionaries and then the value captures; the closure carries
                // both and the SSA `call` prepends them at every application (see the interpreter).
                //
                // Hidden dictionary captures and the environment's own `Value` dictionary are kept
                // symbolic (a static `Dictionary(id)` or a forwarded `@extra` parameter), so both
                // statically-resolved and generic-forwarded closures lower uniformly.

                // The hidden dictionary/evidence captures the lambda body needs, in order.
                let hidden_dicts: Vec<ssa::Value> = n
                    .dictionary_captures
                    .iter()
                    .map(|d| self.lower_extra_argument(&self.hir_arena[*d]))
                    .collect();

                // Resolve the target function reference out of the inner `GetFunction`.
                let function_node = &self.hir_arena[n.function];
                let hir::NodeKind::GetFunction(g) = &function_node.kind else {
                    panic!("BuildClosure.function must be a GetFunction");
                };
                let (fi, mi) = self.resolve_function(g.function);
                let fref = self.demand_function(fi, mi);

                // The symbolic `Value` dictionary used to clone/drop the captured value environment
                // (`None` when there are no value captures).
                let env_dict = n
                    .captures_value_dictionary
                    .map(|d| self.lower_dictionary_operand(&self.hir_arena[d]));

                // Lower each capture to the place of its (already owned) value; the closure moves
                // them into its environment.
                let captures: Vec<ssa::Value> = n
                    .captures
                    .iter()
                    .map(|c| self.lower_as_place(&self.hir_arena[*c]))
                    .collect();

                let closure = self
                    .insert(Instruction::build_closure(
                        node.span,
                        fref,
                        hidden_dicts,
                        env_dict,
                        node.ty,
                        captures,
                    ))
                    .unwrap();
                self.store_into_if_needed(node.span, closure, destination);
            }

            K::CloneClosureEnv(n) => {
                // Deep-clone the captured environment of the source closure, yielding a fresh
                // closure value. This is the body of the generated `Value::clone` for a function
                // type; it is lowered value-returning, so the clone is stored into the destination.
                let source = self.lower_as_place(&self.hir_arena[n.source]);
                let cloned = self
                    .insert(Instruction::clone_closure_env(node.span, source, node.ty))
                    .unwrap();
                self.store_into_if_needed(node.span, cloned, destination);
            }

            K::DropClosureEnv(n) => {
                // Drop the owned captured environment of the target closure. This is the body of the
                // generated `Value::drop` for a function type; it is `()`-typed, so nothing is
                // stored into the destination.
                let target = self.lower_as_place(&self.hir_arena[n.target]);
                self.insert(Instruction::drop_closure_env(node.span, target));
            }

            K::Apply(n) => {
                if n.ty.returns_place() {
                    return self.lower_place_call_into(node, destination);
                }
                // The callee is lowered as a *place*: a function value (in particular a closure) is
                // borrowed in place and read by reference at the call, so it survives repeated calls
                // (`f() + f()`) and is dropped once by its scope cleanup — mirroring the HIR
                // interpreter's `eval_apply`, which calls through a borrow of the function value.
                let f = self.lower_as_place(&self.hir_arena[n.function]);
                let mut arguments: Vec<ssa::Value> = n
                    .arguments
                    .iter()
                    .map(|arg| self.lower_argument(arg))
                    .collect();
                arguments.push(destination.unwrap_or_else(|| self.allocate_result(node, &n.ty)));
                self.emit_call(node.span, f, arguments, &node.effects);
            }

            K::Project(_) | K::ProjectAt(_) => {
                // A projection is a place: copy the field place into the destination (trivial copy;
                // non-trivial reads are wrapped in `CloneValue` by HIR). A bare projection reaching
                // here therefore has a statically sized field type — a generic field is only read
                // through the `Value` dictionary clone of its enclosing `CloneValue`, which lowers
                // the projection as a place (`lower_as_place`) instead.
                if destination.is_some() {
                    self.assert_statically_sized(node.ty);
                    let fp = self.lower_as_place(node);
                    self.memcpy_into_if_needed(node.span, fp, destination);
                }
            }

            K::Loop(n) => {
                // The loop's result is written into `dest` by `break` (or a throwaway temporary
                // when the result is discarded). It is allocated before the stack marker, so it
                // outlives the per-iteration storage reclaimed by `stack_restore`.
                let result = match &destination {
                    Some(dest) => dest.clone(),
                    None => self.alloca_storage(node.span, node.ty),
                };
                // Capture the stack top once before the loop. Every back-edge and exit resets to
                // this marker, so the body's temporaries are reclaimed each iteration. (Owned
                // locals are hoisted to the entry block, below the marker and are unaffected.)
                let marker = self.insert(Instruction::stack_save(node.span)).unwrap();

                let head = self.context.function.add_block().id();
                let exit = self.context.function.add_block().id();
                self.context.loops.insert(
                    n.label,
                    LoopFrame {
                        head,
                        exit,
                        result,
                        marker: marker.clone(),
                        scope_depth: self.context.scopes.len(),
                    },
                );

                // Enter the loop body at its head block.
                self.insert(Instruction::br(node.span, head));
                self.context.point = InsertionPoint::End(head);

                // The body's value is discarded each iteration (the result flows through `break`).
                self.lower_value_into(&self.hir_arena[n.body], None);

                // Back-edge: a body that falls through reclaims its iteration's stack and loops.
                if !self.current_block_is_terminated() {
                    self.insert(Instruction::stack_restore(node.span, marker));
                    self.insert(Instruction::br(node.span, head));
                }

                // Lowering continues after the loop, at its exit block.
                self.context.loops.remove(&n.label);
                self.context.point = InsertionPoint::End(exit);
            }

            K::Break(n) => {
                // Prepare the break value into the loop's result *before* unwinding (a returned
                // local has already been moved out by HIR, so its guarded drop is skipped). Then
                // drop the scopes entered inside the loop, reclaim the iteration's stack, and jump
                // to the loop exit.
                let frame = self.loop_frame(n.label);
                self.lower_value_into(&self.hir_arena[n.value], Some(frame.result));
                // The break value can itself diverge (e.g. `break return x`), terminating the
                // block. In that case the unwind, stack reset, and jump to the loop exit are
                // unreachable and must not be emitted after the terminator.
                if !self.current_block_is_terminated() {
                    self.emit_unwind_drops(node.span, frame.scope_depth);
                    self.insert(Instruction::stack_restore(node.span, frame.marker));
                    self.insert(Instruction::br(node.span, frame.exit));
                }
            }

            K::Continue(n) => {
                // Drop the scopes entered inside the loop, reclaim the iteration's stack, and jump
                // back to the loop head.
                let frame = self.loop_frame(n.label);
                self.emit_unwind_drops(node.span, frame.scope_depth);
                self.insert(Instruction::stack_restore(node.span, frame.marker));
                self.insert(Instruction::br(node.span, frame.head));
            }

            K::ExtractTag(n) => {
                // Read the variant's tag as an `int`. The operand (typically a `LoadLocal` of the
                // scrutinee) is lowered as the variant's place; `extract_tag` reads its tag without
                // consuming the variant, so the payload remains accessible to the match arms.
                let place = self.lower_as_place(&self.hir_arena[*n]);
                let tag = self
                    .insert(Instruction::extract_tag(node.span, place))
                    .unwrap();
                self.store_into_if_needed(node.span, tag, destination);
            }

            K::Variant(n) => {
                // Construct a tagged variant. With no destination the construction is discarded, so
                // only the payload's effects are lowered.
                let payload = &self.hir_arena[n.payload];
                let Some(dest) = destination else {
                    self.lower_value_into(payload, None);
                    return;
                };
                // Build the variant in place: store a tagged shell into the destination, then fill
                // its payload slot directly. Building in place (rather than materializing the
                // payload aggregate into a temporary that is then wrapped) means the payload — which
                // may be generic, e.g. the `(A,)` of `Some(a)` — is never allocated as whole-aggregate
                // storage, which would require a `Value` layout witness for the payload type the
                // enclosing function does not carry. Only the payload's leaves are stored, each
                // through its own (available) witness.
                let shell = self
                    .insert(Instruction::variant(node.span, n.tag, node.ty))
                    .unwrap();
                self.store(node.span, shell, dest.clone());
                let payload_place = self
                    .insert(Instruction::subfield(
                        node.span,
                        dest,
                        int_constant(0),
                        payload.ty,
                    ))
                    .unwrap();
                self.lower_value_into(payload, Some(payload_place));
            }

            K::LoadDictionary(n) => {
                // A required dictionary/evidence resolves to its incoming extra parameter, which is a
                // place. Copy it into the destination if one is requested.
                if destination.is_some() {
                    let p = self.context.extra_parameters[&n.extra_parameter].clone();
                    self.memcpy_into_if_needed(node.span, p, destination);
                }
            }

            K::CallDictionaryMethod(n) => {
                // A place-returning method is resolved as a place and copied into the destination,
                // like any other place-returning call.
                if n.ty.returns_place() {
                    return self.lower_place_call_into(node, destination);
                }
                // Project the method out of the dictionary, load it, then call it into the
                // destination (or a throwaway result for a discarded call).
                let (method, mut arguments) = self.lower_dictionary_method_target(node, n);
                arguments.push(destination.unwrap_or_else(|| self.allocate_result(node, &n.ty)));
                self.emit_call(node.span, method, arguments, &node.effects);
            }

            // Runtime guards have no SSA representation yet; they lower to nothing.
            K::CheckCallDepth | K::CheckFuel => {}

            K::Tuple(ns) => self.lower_aggregate_into(node, ns, destination),

            K::Record(ns) => self.lower_aggregate_into(node, ns, destination),

            K::Uninit => self.store(
                node.span,
                ssa::Value::Uninit(ShownType {
                    ty: node.ty,
                    name: self.show(node.ty),
                }),
                destination.expect("discarded uninit construction is not yet implemented"),
            ),

            K::WithPlace(n) => {
                // An addressor subscript site: bind the accessor's place, then lower the body
                // (which reads the binding) into the destination.
                self.bind_local_for_with_place(n);
                self.lower_value_into(&self.hir_arena[n.body], destination);
            }

            K::WithYielded(n) => {
                // A scoped subscript site: `project` the accessor to its yield and bind the yielded
                // place, lower the body (which reads/writes the binding) into the destination, then
                // `exit_scope` emits the `end_project` that runs the accessor slide. The slide also
                // runs on a transfer or error out of the body (the scope's cleanup action is part of
                // the unwind/pad path). Mirrors `eval_with_yielded`.
                self.lower_with_yielded_enter(n);
                self.lower_value_into(&self.hir_arena[n.body], destination);
                self.exit_scope(node.span);
            }

            K::GetDictionaryAssociatedConst(c) => {
                // Read an associated const out of a dictionary: project the entry's place by its
                // index, then copy the value into the destination (if one is requested).
                // Mirrors the interpreter's `eval_get_dictionary_associated_const`.
                if destination.is_some() {
                    let dictionary = self.lower_dictionary_operand(&self.hir_arena[c.dictionary]);
                    let const_place = self
                        .insert(Instruction::dict_entry(
                            node.span,
                            dictionary,
                            c.entry_index.as_index(),
                            node.ty,
                        ))
                        .unwrap();
                    self.memcpy_into_if_needed(node.span, const_place, destination);
                }
            }

            K::GetDictionaryMethod(_) => {
                // A trait method as a first-class value: take its `dict_entry` place (see
                // `lower_as_place`) and copy the (trivially-copyable, bare) function value into the
                // destination, like reading any other dictionary entry.
                if destination.is_some() {
                    let method_place = self.lower_as_place(node);
                    self.memcpy_into_if_needed(node.span, method_place, destination);
                }
            }
            K::Return(n) => {
                // `return <expr>` writes into the function's return out-pointer and terminates,
                // ignoring the ambient `destination`. Mirrors the interpreter's `eval_return`:
                // a place-returning function returns the `*T` place pointer; otherwise the value.
                let operand = &self.hir_arena[*n];
                let dest = self.context.return_destination.clone();
                if self.context.returns_place {
                    let place = self.lower_as_place(operand);
                    self.store(node.span, place, dest);
                } else {
                    self.lower_value_into(operand, Some(dest));
                }
                // Unwind every enclosing scope: drop all owned locals (innermost first) before
                // returning. The result has already been moved into the out-pointer, so a returned
                // local reads as uninitialized and its guarded drop is skipped.
                self.emit_return_drops(node.span);
                self.insert(Instruction::ret(node.span));
            }

            K::Yield(place_node) => {
                // Inside a `YieldedOnce` accessor body: expose the yielded place to the driving
                // `project` and suspend. The place flows out through the `yield` (not the return
                // out-pointer), so the ambient `destination` is irrelevant — the accessor is driven
                // with none. Mirrors the HIR interpreter's `eval_yield`. The instructions emitted
                // after this (the slide) run only when `end_project` resumes the accessor.
                let place = self.lower_as_place(&self.hir_arena[*place_node]);
                self.insert(Instruction::r#yield(node.span, place));
            }

            K::Array(ids) => self.lower_array_into(node, ids, destination),

            _ => {
                todo!(
                    "lowering is unimplemented for node of kind '{:?}'",
                    node.kind
                );
            }
        }
    }

    /// Returns the lowered representation of the given native value.
    fn lower_as_primitive(&mut self, native: &LiteralValue) -> Option<ssa::Value> {
        use ssa::value::Integer as Int;

        if native.as_primitive_ty::<()>().is_some() {
            Some(ssa::Value::Unit)
        } else if let Some(n) = native.as_primitive_ty::<isize>() {
            Some(ssa::Value::Integer(containers::b(Int::from_isize(*n))))
        } else if let Some(n) = native.as_primitive_ty::<u32>() {
            Some(ssa::Value::Integer(containers::b(Int::from_u32(*n))))
        } else if let Some(n) = native.as_primitive_ty::<i32>() {
            Some(ssa::Value::Integer(containers::b(Int::from_i32(*n))))
        } else if let Some(x) = native.as_primitive_ty::<Float>() {
            // A `Float` is always finite and never NaN, so it converts to a `NotNan` infallibly.
            Some(ssa::Value::Float(
                NotNan::new(x.into_inner()).expect("a Float is never NaN"),
            ))
        } else if let Some(s) = native.as_primitive_ty::<crate::std::string::String>() {
            Some(ssa::Value::String(s.clone()))
        } else {
            native
                .as_primitive_ty::<bool>()
                .map(|n| ssa::Value::Boolean(*n))
        }
    }

    /// Inserts `s` at the current insertion point, and returns its result register, if any.
    fn insert(&mut self, s: Instruction) -> Option<ssa::Value> {
        let i = match &self.context.point {
            InsertionPoint::End(b) => self.context.function.block_mut(*b).append(s),
        };
        self.context.function.definition(i)
    }

    /// Returns whether the current insertion block already ends in a terminator (e.g. a `ret`
    /// emitted by an explicit `return`), so callers can avoid inserting after a terminator.
    fn current_block_is_terminated(&self) -> bool {
        match &self.context.point {
            InsertionPoint::End(b) => self.context.function.block(*b).is_terminated(),
        }
    }

    /// Returns a textual representation of `x`.
    fn show<T: FormatWith<ModuleEnv<'a>>>(&self, x: T) -> String {
        let e = ModuleEnv::new(self.module, self.others);
        format!("{}", x.format_with(&e))
    }
}

/// The context in which instructions are inserted.
struct InsertionContext {
    /// The function in which new instructions are inserted.
    function: ssa::Function,

    /// The function we are lowering from.
    source: LocalFunctionId,

    /// Where new instructions are inserted in `function`.
    point: InsertionPoint,

    /// The source region with which inserted instructions are associated.
    span: Location,

    /// The SSA places (pointer values) backing the function's locals, including explicit arguments
    /// (each passed by pointer) and any variables declared within the function.
    locals: FxHashMap<LocalDeclId, ssa::Value>,

    /// The SSA values bound to extra parameters of the function.
    extra_parameters: FxHashMap<ExtraParameterId, ssa::Value>,

    /// The `Value` dictionary parameters witnessing the run-time layout of generic types, used to
    /// allocate storage whose size is known only at run time.
    value_witnesses: Vec<(Type, ssa::Value)>,

    /// The lexically enclosing loops, keyed by `LoopId`, used to lower `break`/`continue`.
    loops: FxHashMap<LoopId, LoopFrame>,

    /// The return out-pointer (the last parameter) into which the function writes its result.
    return_destination: ssa::Value,

    /// Whether the lowered function itself returns a place (`FnReturnConvention::AddressorPlace`).
    /// When set, `return <expr>` lowers `<expr>` as a place and stores that pointer into the
    /// `**T` return out-pointer (mirrors the interpreter's `EvalCtx::returns_place`).
    returns_place: bool,

    /// The stack of active lexical scopes, innermost last. Each scope records the drop obligations
    /// of the locals it owns; the obligations are emitted as inline (init-guarded) `drop`
    /// instructions at every control-transfer edge that unwinds the scope: a normal block exit
    /// drops its own scope, and a `return` drops all enclosing scopes.
    scopes: Vec<Scope>,

    /// Cleanup landing pads whose bodies are emitted at function finalization rather than where they
    /// are referenced. A pad block is *allocated* (empty) the moment a fallible `invoke` needs to
    /// name it, but cannot be *filled* there: a block is a contiguous range in the shared instruction
    /// arena, so emitting the pad's drops mid-body would splice them into the block being lowered.
    /// Each pad therefore captures its drop obligations (and the outer pad it chains to) up front and
    /// is filled, contiguously, after the body is fully lowered (see `fill_pending_pads`).
    pending_pads: Vec<PendingPad>,
}

/// A cleanup landing pad awaiting its body (see `InsertionContext::pending_pads`).
struct PendingPad {
    /// The (allocated, initially empty) pad block.
    block: BlockIdentity,

    /// This scope's cleanup actions to run in the pad, already reversed (innermost-declared last runs
    /// first), captured when the pad was allocated and the scope was still live.
    actions: Vec<CleanupAction>,

    /// The pad of the nearest enclosing scope with obligations, branched to after this pad's actions;
    /// `None` for the outermost pad, which `resume`s instead (re-raising to the caller).
    outer: Option<BlockIdentity>,

    /// The span the pad's actions are attributed to (the first fallible call that needed the pad).
    span: Location,
}

/// A lexical scope's deferred cleanup actions (in declaration order).
struct Scope {
    /// The cleanup to run when the scope exits — owned-local drops, and, for the dedicated scope a
    /// `WithYielded` opens, the `end_project` that runs the accessor slide. Run in reverse order on
    /// every exit (normal, transfer, and the error pad), so the slide runs after the body's own
    /// drops, on every path — matching the HIR interpreter's epilogue-on-exit.
    actions: Vec<CleanupAction>,

    /// The cleanup landing pad for this scope, built lazily the first time a fallible call nested in
    /// it needs an unwind edge (see `allocate_pad`). The pad runs this scope's actions (reverse
    /// declaration order, init-guarded) and then chains to the nearest enclosing scope's pad or, if
    /// none, `resume`s — re-raising the in-flight error to the caller. `None` until built (a scope
    /// with no obligations, or one no fallible call unwinds through, never gets one).
    pad: Option<BlockIdentity>,
}

/// A single deferred cleanup action run on scope exit, transfer, and the error pad.
#[derive(Clone)]
enum CleanupAction {
    /// Drop an owned local (init-guarded `Value::drop`).
    Drop(DropObligation),

    /// Close a scoped subscript: run the accessor slide and reclaim its frame (`end_project` of the
    /// place a `project` exposed). The projection binding is non-owning, so there is no drop.
    EndProject { place: ssa::Value },
}

/// The lowering targets of an enclosing loop, used to resolve `break`/`continue` to it.
#[derive(Clone)]
struct LoopFrame {
    /// The loop's head block, branched to by `continue` and by the body's back-edge.
    head: BlockIdentity,

    /// The loop's exit block, branched to by `break`; lowering continues here after the loop.
    exit: BlockIdentity,

    /// The place into which `break` writes the loop's result (the loop's destination, or a
    /// throwaway temporary when the result is discarded).
    result: ssa::Value,

    /// The stack marker captured before the loop; every iteration is reset to it, and `break`/
    /// `continue` reset to it before transferring, so per-iteration temporaries do not leak.
    marker: ssa::Value,

    /// The scope-stack depth at loop entry. A `break`/`continue` unwinds the scopes above this
    /// depth (the ones entered inside the loop body) before transferring.
    scope_depth: usize,
}

/// A single deferred drop: the place to drop, the type of its pointee (to resolve a dictionary
/// `Value::drop` method), and how to dispatch the drop.
#[derive(Clone)]
struct DropObligation {
    place: ssa::Value,
    dropped_ty: Type,
    spec: DropSpec,
}

/// Whether a call whose evaluation carries `effects` may raise a runtime error, and so needs an
/// unwind edge to a cleanup pad. A concrete `Fallible` primitive effect is exact; an unresolved
/// effect variable is treated conservatively as potentially fallible, so a generic callee that
/// instantiates fallibly still runs its caller's cleanup on the error path.
fn effects_are_fallible(effects: &EffType) -> bool {
    effects.contains(Effect::Primitive(PrimitiveEffect::Fallible)) || effects.has_variables()
}

/// How a `Value::drop` is dispatched for a drop obligation.
#[derive(Clone, Copy)]
enum DropSpec {
    /// A concrete `Value::drop` implementation.
    Static(FunctionReference),
    /// `Value::drop` loaded at run time from this hidden dictionary extra parameter.
    Dictionary(ExtraParameterId),
}

/// Where an instruction should be inserted in a basic block.
#[derive(Clone, Copy)]
enum InsertionPoint {
    /// The end of a basic block.
    End(BlockIdentity),
}
