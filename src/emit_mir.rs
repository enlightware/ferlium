// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use crate::FxHashMap;
use ustr::Ustr;

use crate::hir::function::ArgConvention;
use crate::mir::{
    Instantiation, Operation, builder::FunctionBuilder, operation::SourceFallibility,
    terminator::Terminator,
};
use crate::module::{
    ExtraParameterId, ResolvedLocalClone, ResolvedLocalDrop, ResolvedTakeLocalValueMode,
};
use crate::types::r#trait::{TraitDictionaryEntryIndex, TraitMethodIndex};
use crate::types::r#type::{CallImplType, CallResultConvention, FnType, SubscriptResultConvention};
use crate::{
    Location, Modules, containers,
    format::FormatWith,
    hir::{
        self, CallArgument, Case, ENode, ENodeArena, Elaborated, GetDictionary, LoopId,
        dictionary::DictionaryReq, value::LiteralValue,
    },
    mir::{self, BlockId},
    module::{
        self, FunctionId, LocalDeclId, LocalFunctionId, Module, ModuleEnv, ModuleId,
        TraitDictionaryId, TraitImplId, id::Id,
    },
    std::{
        STD_MODULE_ID,
        core_traits_names::VALUE_TRAIT_NAME,
        value::{VALUE_CLONE_METHOD_INDEX, VALUE_DROP_METHOD_INDEX, type_has_static_layout},
    },
    types::{effects::no_effects, r#type::Type, type_properties::concrete_type_is_trivial_copy},
};

/// Emits the textual representation of the Ferlium MIR of `module`.
///
/// Every lowerable local function of `module` is emitted, including the (anonymous) member
/// functions of its subscripts. A `YieldedOnce` subscript member is emitted standalone as a
/// suspendable function (its `yield` exposes the yielded place to the driving `project`). Only
/// bodiless (native) functions are skipped.
///
/// Intended for testing and debugging.
pub(crate) fn emit_mir(
    module: &Module,
    others: &Modules,
    artifacts: &crate::compiler::MirArtifacts,
) -> String {
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
    let env = ModuleEnv::new(module, others);
    let declared = functions.into_iter().map(|(_, f)| {
        let lowered = artifacts
            .get(f)
            .expect("every script function must have a MIR artifact");
        format!("{}", lowered.format_with(&env))
    });
    // Specialized bodies have no entry in the function table above — nothing in the source declared
    // them — so they are appended in creation order, each under the generated name saying which
    // original and which instantiation it came from. Without this a dump would show call sites
    // reaching bodies it never printed.
    let specialized = artifacts.specializations().iter().map(|specialization| {
        format!(
            "// specialization of {}\n{}",
            mir::Value::Function(specialization.original).format_with(&env),
            specialization.body.format_with(&env)
        )
    });
    declared.chain(specialized).collect::<Vec<_>>().join("\n")
}

/// The MIR blocks involved in the lowering of a case in a match expression.
struct CaseBlocks {
    /// The head blocks for the conditions.
    heads: Vec<BlockId>,

    /// The body blocks for the conditions.
    bodies: Vec<BlockId>,

    /// The default case block.
    default: BlockId,

    /// The tail block of the case.
    tail: BlockId,
}

/// Lowers elaborated HIR into MIR.
struct Emitter<'a> {
    /// Read-only access to the completed module and its dependencies.
    env: ModuleEnv<'a>,

    /// The context in which the emitter inserts new IR.
    context: InsertionContext,

    /// The HIR node arena.
    hir_arena: &'a ENodeArena,
}

/// Builds the MIR of the function `source` of `module` and returns the lowered function.
///
/// This is the shared entry point used both by the textual MIR dump (`emit_mir`) and by backends
/// (such as a future Wasm emitter) that consume the lowered `mir::Function` directly.
pub fn build_mir_function(source: LocalFunctionId, env: ModuleEnv<'_>) -> mir::Function {
    Emitter::build_mir_fn(source, env)
}

impl<'a> Emitter<'a> {
    /// Builds and returns the lowered MIR representation of `source`.
    fn build_mir_fn(source: LocalFunctionId, env: ModuleEnv<'a>) -> mir::Function {
        let module = env.current;
        let others = env.modules;
        let f = module.get_function_by_id(source).unwrap();
        let syntax = f
            .code
            .as_ref()
            .as_script()
            .expect("function should be a script");

        let name = module.get_function_name_by_id(source).unwrap();
        let mut lowered = FunctionBuilder::new(name, f.definition.return_convention());

        // The function signature is laid out as `[extra dictionary/evidence params..., runtime
        // args...]`. Extra parameters occupy the leading slots and the visible runtime arguments,
        // which are the leading `LocalDecl`s, follow them.
        let env = ModuleEnv::new(module, others);
        let extra = f.definition.ty_scheme.extra_parameters(env);

        // Record the extra parameters in signature order and which incoming dictionary parameter
        // witnesses the `Value` layout of each generic type, so allocations of generic storage can
        // carry their run-time layout witness.
        let mut extra_parameters: FxHashMap<ExtraParameterId, mir::Value> = FxHashMap::default();
        let value_trait_id = env.expect_std_trait_id(VALUE_TRAIT_NAME);
        let mut value_witnesses: Vec<(Type, mir::Value)> = vec![];
        for (j, req) in extra.requirements.iter().enumerate() {
            let parameter = mir::Value::Parameter(lowered.add_parameter(
                req.to_dict_type_in_env(&env),
                mir::ParameterKind::Dictionary,
            ));
            extra_parameters.insert(ExtraParameterId::from_index(j), parameter.clone());
            if let DictionaryReq::TraitImpl {
                trait_id,
                input_tys,
                ..
            } = req
                && *trait_id == value_trait_id
                && let [ty] = input_tys[..]
            {
                value_witnesses.push((ty, parameter));
            }
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
        let mut locals: FxHashMap<LocalDeclId, mir::Value> = FxHashMap::default();
        for i in 0..runtime_arg_count {
            let passing = if i < capture_count {
                // A captured-environment slot is handed to the body as a mutable reference into the
                // (per-call cloned) environment.
                ArgConvention::MutableRef
            } else {
                f.parameter_passing[i - capture_count]
            };
            let param = mir::Value::Parameter(
                lowered.add_parameter(f.locals[i].ty, mir::ParameterKind::Parameter(passing)),
            );
            locals.insert(LocalDeclId::from_index(i), param);
        }

        // Append the return out-pointer as the last parameter. It is present unconditionally, even
        // when the return type is `()`: the function writes its result through this pointer and then
        // returns with no operand.
        let return_type = f.definition.ty_scheme.ty.ret;
        let return_destination =
            mir::Value::Parameter(lowered.add_parameter(return_type, mir::ParameterKind::Return));

        // Create the function's entry.
        let entry = lowered.add_block();
        let code = &module.hir_arena[syntax.entry_node_id];
        let span = code.span;

        // Instantiate an emitter to generate the function's contents.
        let mut emitter = Emitter {
            env,
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
                cleanup_unwind_target: CleanupUnwindTarget::CurrentScope,
                propagate_error_block: None,
                failure_during_cleanup_block: None,
            },
            hir_arena: &module.hir_arena,
        };

        // Allocate frame storage for every `Owned` local and bind it to its `alloca` place.
        emitter.allocate_owned_locals();

        // Lower the body, dispatching on the function's return convention.
        match f.definition.return_convention() {
            // A value-returning function stores its result into the return out-pointer.
            CallResultConvention::Value => {
                let ret_dest = emitter.context.return_destination.clone();
                emitter.lower_value_into(code, Some(ret_dest));
            }
            // An addressor function returns a caller-rooted place. Its body is `never`-typed and
            // ends in `return <place-expr>` (enforced at `CallableDefinition::returns_place`
            // validation); the embedded `Return` stores the place pointer into the return
            // out-pointer. Driving with no destination avoids a spurious value store.
            CallResultConvention::Subscript(SubscriptResultConvention::AddressorPlace) => {
                emitter.lower_value_into(code, None);
            }
            // A `YieldedOnce` member is a suspendable accessor: its body is `never`-typed, runs its
            // ramp, and ends (in block-structured position) at a `Yield(place)` that exposes the
            // yielded place and suspends; the explicit resume block is the slide (epilogue), reached
            // when the driving `WithYielded` resumes via `end_project`. Like an addressor it
            // produces no value, so it is driven with no destination (the `Yield` itself exposes the
            // place; no spurious value store).
            CallResultConvention::Subscript(SubscriptResultConvention::YieldedOnce) => {
                emitter.lower_value_into(code, None);
            }
        }

        // Append the trailing return terminator.
        if !emitter.current_block_is_terminated() {
            emitter.terminate(Terminator::ret(emitter.context.span));
        }

        // Fill cleanup blocks after the body. Their identities can be referenced before their
        // operations and terminators are known because only the builder admits pending blocks.
        emitter.fill_pending_pads();

        let env = emitter.env;
        emitter.context.function.finish(env)
    }

    /// Returns the module-qualified identity of `f`.
    fn demand_function(&self, f: LocalFunctionId, module_identity: ModuleId) -> FunctionId {
        FunctionId::new(module_identity, f)
    }

    /// Resolves a [`FunctionId`] to the `(LocalFunctionId, ModuleId)` pair identifying the function
    /// within its defining module. `FunctionId` is module-qualified, so this just reads its fields.
    fn resolve_function(&self, function: FunctionId) -> (LocalFunctionId, ModuleId) {
        (function.function, function.module)
    }

    /// Builds an [`mir::Value`] referencing the given function.
    fn function_value(&self, function: FunctionId) -> mir::Value {
        let (fi, mi) = self.resolve_function(function);
        mir::Value::Function(self.demand_function(fi, mi))
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
        source: mir::Value,
        target: mir::Value,
    ) {
        // The dictionary is a forwarded `@extra` parameter — a symbolic dictionary operand.
        let dictionary = self.context.extra_parameters[&dictionary].clone();
        let (entry_index, method_ty) = self.value_method(VALUE_CLONE_METHOD_INDEX, cloned_ty);
        let method_place = self
            .insert(Operation::dict_entry(
                span,
                dictionary,
                entry_index,
                method_ty,
            ))
            .unwrap();
        // The callee is the place of the `Value::clone` method entry; the clone reads the function
        // value by reference (never loaded into a register — the same callee contract as `call`).
        self.insert(Operation::clone_value(
            span,
            source,
            target,
            method_place,
            cloned_ty,
        ));
    }

    /// Returns the runtime dictionary entry index and function type of the `Value` trait method
    /// `method_index` (e.g. [`VALUE_DROP_METHOD_INDEX`] or [`VALUE_CLONE_METHOD_INDEX`]) for the
    /// type `ty`.
    fn value_method(
        &self,
        method_index: TraitMethodIndex,
        ty: Type,
    ) -> (TraitDictionaryEntryIndex, Type) {
        let value_trait_id = self.env.expect_std_trait_id(VALUE_TRAIT_NAME);
        let trait_def = self.env.trait_def(value_trait_id);
        let dict_ty = trait_def.get_dictionary_type_for_tys(&[ty], &[], &[]);
        let entry_index = trait_def.dictionary_method_index(method_index);
        let dict_ty_data = dict_ty.data();
        let method_ty = dict_ty_data
            .as_tuple()
            .expect("Value dictionary should be a tuple type")[entry_index.as_index()];
        (entry_index, method_ty)
    }

    /// Returns the `Value::drop` sibling of the statically resolved `Value::clone` method `clone`:
    /// the drop method of the same concrete `Value` impl. Elaboration resolves clone/drop dispatch
    /// per *local*; an emitter-synthesized clone-source temporary has no local to carry a drop
    /// resolution, so its drop is recovered from the impl the clone came from.
    fn value_drop_sibling_of_clone(&self, clone: FunctionId) -> FunctionId {
        let value_trait_id = self.env.expect_std_trait_id(VALUE_TRAIT_NAME);
        let trait_def = self.env.trait_def(value_trait_id);
        let clone_index = trait_def
            .dictionary_method_index(VALUE_CLONE_METHOD_INDEX)
            .as_index();
        let drop_index = trait_def
            .dictionary_method_index(VALUE_DROP_METHOD_INDEX)
            .as_index();
        let module = self.env.module_by_id(clone.module).unwrap_or_else(|| {
            panic!("module {} is unavailable during MIR lowering", clone.module)
        });
        // The compiler-provided `Value` methods of function types are module-wide named
        // functions, not impl members; resolve the drop sibling by its well-known name.
        if module.get_function_name_by_id(clone.function)
            == Some(crate::std::value::function_value_method_name(
                VALUE_CLONE_METHOD_INDEX,
            ))
        {
            let drop_fn = module
                .get_local_function_id(crate::std::value::function_value_method_name(
                    VALUE_DROP_METHOD_INDEX,
                ))
                .expect("a module with a function-value clone must also provide its drop");
            return self.demand_function(drop_fn, clone.module);
        }
        let impls = &module.impls;
        let drop_fn = impls
            .data
            .iter()
            .enumerate()
            .filter(|(i, _)| {
                match impls.get_key_by_local_id(module::trait_impl::LocalImplId::from_index(*i)) {
                    Some(key) => key.trait_id() == value_trait_id,
                    // A generated (anonymous) dictionary impl — e.g. the compiler-provided
                    // `Value` impl of a function type — has no key; keep it as a candidate.
                    None => true,
                }
            })
            .find_map(|(_, imp)| {
                (imp.methods.get(clone_index) == Some(&clone.function))
                    .then(|| imp.methods.get(drop_index).copied())
                    .flatten()
            })
            .unwrap_or_else(|| panic!("no Value impl provides the clone method {clone:?}"));
        self.demand_function(drop_fn, clone.module)
    }

    /// Lowers the source of a `Value::clone` to the place the clone reads, together with the drop
    /// obligation of the temporary backing it, if any.
    ///
    /// A place-yielding source is borrowed in place — nothing to drop. A value source (e.g. a
    /// nested clone) is materialized into a fresh temporary the clone borrows; the HIR interpreter
    /// transfers such a value into the callee's frame, but in the by-pointer MIR ABI every
    /// argument is borrowed, so the temporary stays owned by this frame and the caller must emit
    /// its init-guarded `drop` — derived from the clone dispatch (the same impl's `Value::drop`,
    /// or the same dictionary's drop entry) — after the clone call.
    fn lower_clone_source(
        &mut self,
        clone: &ResolvedLocalClone,
        node: &ENode,
    ) -> (mir::Value, Option<DropSpec>) {
        if self.node_yields_place(node) {
            return (self.lower_as_place(node), None);
        }
        let temp = self.alloca_storage(node.span, node.ty);
        self.lower_value_into(node, Some(temp.clone()));
        let spec = match clone {
            ResolvedLocalClone::TrivialCopy => None,
            ResolvedLocalClone::Static(f) => {
                Some(DropSpec::Static(self.value_drop_sibling_of_clone(*f)))
            }
            ResolvedLocalClone::Dictionary(extra) => Some(DropSpec::Dictionary(*extra)),
        };
        (temp, spec)
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

    /// Emits a single init-guarded `drop` operation for the obligation `(place, dropped_ty, spec)`,
    /// materializing the `Value::drop` callee (a constant for a static drop, or a dictionary load for
    /// a dictionary drop). Does nothing if the current block is already terminated.
    fn emit_drop(&mut self, span: Location, place: mir::Value, dropped_ty: Type, spec: DropSpec) {
        if self.current_block_is_terminated() {
            return;
        }
        let callee = match spec {
            DropSpec::Static(fref) => mir::Value::Function(fref),
            DropSpec::Dictionary(dictionary) => {
                // The dictionary is a forwarded `@extra` parameter — a symbolic dictionary operand.
                let dictionary = self.context.extra_parameters[&dictionary].clone();
                let (entry_index, method_ty) =
                    self.value_method(VALUE_DROP_METHOD_INDEX, dropped_ty);
                // The callee is the place of the `Value::drop` method entry; the `drop` reads the
                // function value by reference (never loaded — same callee contract as `call`).
                self.insert(Operation::dict_entry(
                    span,
                    dictionary,
                    entry_index,
                    method_ty,
                ))
                .unwrap()
            }
        };
        self.insert(Operation::drop(span, place, callee, dropped_ty));
    }

    /// Builds the drop actions of the owned, non-`Skip` locals listed in `cleanup` (in declaration
    /// order).
    fn drop_actions(&mut self, cleanup: &[LocalDeclId]) -> Vec<CleanupAction> {
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
        actions
    }

    /// Pushes a new lexical scope whose drop obligations are the owned, non-`Skip` locals listed in
    /// `cleanup` (in declaration order).
    fn enter_scope(&mut self, cleanup: &[LocalDeclId]) {
        let actions = self.drop_actions(cleanup);
        self.context.scopes.push(Scope { actions, pad: None });
    }

    /// Emits a single cleanup action (a drop, or the `end_project` that runs an accessor slide). Does
    /// nothing if the current block is already terminated, mirroring `emit_drop`.
    fn emit_cleanup(&mut self, span: Location, action: CleanupAction) {
        match action {
            CleanupAction::Drop(o) => self.emit_drop(span, o.place, o.dropped_ty, o.spec),
            CleanupAction::EndProject { place, call_ty } => {
                if !self.current_block_is_terminated() {
                    let operation = Operation::end_project(span, place);
                    if call_type_is_fallible(&call_ty) {
                        self.invoke(operation);
                    } else {
                        self.insert_infallible(operation);
                    }
                }
            }
        }
    }

    /// Pops the innermost scope, then emits its cleanup in reverse declaration order (normal scope
    /// exit). If an action raises, its error edge runs the still-pending actions from this scope,
    /// followed by the enclosing scopes, without retrying the action that already started.
    fn exit_scope(&mut self, span: Location) {
        let scope = self
            .context
            .scopes
            .pop()
            .expect("exit_scope without a matching enter_scope");
        let actions: Vec<CleanupAction> = scope.actions.into_iter().rev().collect();
        let outer = if actions.iter().any(CleanupAction::is_source_fallible) {
            self.innermost_pad(span)
        } else {
            None
        };
        self.emit_inline_cleanup_actions(span, actions, outer);
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
        debug_assert!(matches!(
            self.context.cleanup_unwind_target,
            CleanupUnwindTarget::CurrentScope
        ));
        for depth in (to_depth..self.context.scopes.len()).rev() {
            let actions: Vec<CleanupAction> = self.context.scopes[depth]
                .actions
                .iter()
                .rev()
                .cloned()
                .collect();
            let outer = if actions.iter().any(CleanupAction::is_source_fallible) {
                self.context.scopes[..depth]
                    .iter()
                    .rposition(|scope| !scope.actions.is_empty())
                    .map(|outer_depth| self.allocate_pad(outer_depth, span))
            } else {
                None
            };
            self.emit_inline_cleanup_actions(span, actions, outer);
        }
    }

    /// Emits cleanup performed by a normal scope exit or control transfer.
    ///
    /// A source failure from one action becomes the primary failure. Its error edge enters a pad
    /// containing only the actions that have not started yet, then continues through `outer`.
    /// Cleanup inside that pad is already unwinding, so another source failure poisons execution.
    fn emit_inline_cleanup_actions(
        &mut self,
        span: Location,
        actions: Vec<CleanupAction>,
        outer: Option<BlockId>,
    ) {
        for (index, action) in actions.iter().cloned().enumerate() {
            if action.is_source_fallible() {
                let remaining = actions[index + 1..].to_vec();
                let error_target = if remaining.is_empty() {
                    outer
                } else {
                    Some(self.allocate_actions_pad(remaining, outer, span))
                };
                self.context.cleanup_unwind_target = match error_target {
                    Some(target) => CleanupUnwindTarget::Pad(target),
                    None => CleanupUnwindTarget::PropagateWithoutPad,
                };
            }
            self.emit_cleanup(span, action);
        }
        self.context.cleanup_unwind_target = CleanupUnwindTarget::CurrentScope;
    }

    /// Emits the drops of *all* enclosing scopes, innermost first (the unwinding performed by a
    /// `return`).
    fn emit_return_drops(&mut self, span: Location) {
        self.emit_unwind_drops(span, 0);
    }

    /// Allocates (or returns the cached) cleanup pad the current exceptional edge should unwind to,
    /// plus the outer pads it chains to. The pad blocks are created empty here and recorded in
    /// `pending_pads`; their bodies are emitted at function finalization (see `fill_pending_pads`).
    /// Returns `None` when no enclosing scope has drop
    /// obligations — the frame has nothing to clean up, so the source failure propagates
    /// straight to the caller.
    fn innermost_pad(&mut self, span: Location) -> Option<BlockId> {
        let depth = self
            .context
            .scopes
            .iter()
            .rposition(|scope| !scope.actions.is_empty())?;
        Some(self.allocate_pad(depth, span))
    }

    /// Allocates the cleanup pad block for the scope at `depth` (memoized on the scope), recursively
    /// allocating the chain of enclosing pads, and records each in `pending_pads` for later filling.
    /// If cleanup completes, the chained pads, innermost first, drop every live frame local exactly
    /// once on the error path — mirroring the inline unwinding
    /// `emit_unwind_drops`/`emit_return_drops` perform for `break`/`return`, but reached via an
    /// explicit source-error edge.
    fn allocate_pad(&mut self, depth: usize, span: Location) -> BlockId {
        if let Some(pad) = self.context.scopes[depth].pad {
            return pad;
        }
        let pad = self.context.function.add_block();
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

    /// Allocates an uncached pad for the pending suffix of an inline cleanup sequence.
    ///
    /// Unlike [`allocate_pad`](Self::allocate_pad), `actions` deliberately excludes the cleanup
    /// action whose primary failure enters this pad, so that action cannot be retried.
    fn allocate_actions_pad(
        &mut self,
        actions: Vec<CleanupAction>,
        outer: Option<BlockId>,
        span: Location,
    ) -> BlockId {
        debug_assert!(!actions.is_empty());
        let block = self.context.function.add_block();
        self.context.pending_pads.push(PendingPad {
            block,
            actions,
            outer,
            span,
        });
        block
    }

    /// Fills all deferred cleanup blocks at function finalization. A block runs its cleanup, then
    /// branches to its enclosing cleanup or terminates with `propagate_error`. A source-fallible
    /// cleanup action uses `failure_during_cleanup` as its error successor: a second source failure
    /// poisons the executor instead of starting a replacement unwind.
    fn fill_pending_pads(&mut self) {
        let pads = std::mem::take(&mut self.context.pending_pads);
        for pad in pads {
            self.context.point = InsertionPoint::End(pad.block);
            debug_assert!(matches!(
                self.context.cleanup_unwind_target,
                CleanupUnwindTarget::CurrentScope
            ));
            self.context.cleanup_unwind_target = CleanupUnwindTarget::FailureDuringCleanup;
            for action in pad.actions {
                self.emit_cleanup(pad.span, action);
            }
            self.context.cleanup_unwind_target = CleanupUnwindTarget::CurrentScope;
            match pad.outer {
                Some(outer_pad) => self.terminate(Terminator::goto(pad.span, outer_pad)),
                None => self.terminate(Terminator::propagate_error(pad.span)),
            };
        }
    }

    /// Emits a call using its retained instantiated call-site type. A source-fallible call becomes
    /// an `invoke` with explicit normal and source-error successors, even when the error successor
    /// merely propagates. A proven source-infallible call remains an ordinary operation. Sandbox
    /// violations bypass both successors.
    fn emit_call(
        &mut self,
        span: Location,
        callee: mir::Value,
        arguments: Vec<mir::Value>,
        ty: &CallImplType,
        instantiation: Option<Instantiation>,
    ) {
        self.insert(Operation::instantiated_call(
            span,
            callee,
            arguments,
            ty.clone(),
            instantiation,
        ));
    }

    /// The instantiation to record on a call, from the HIR call node's data.
    ///
    /// `None` when the callee is not generic, which is the common case and what keeps the operand
    /// off most operations. See `doc/generic-instantiation.md`.
    fn instantiation_of(inst_data: &hir::FnInstData) -> Option<Instantiation> {
        if inst_data.ty_args.is_empty() && inst_data.eff_args.is_empty() {
            return None;
        }
        Some(Instantiation {
            ty_args: inst_data.ty_args.clone(),
            eff_args: inst_data.eff_args.clone(),
        })
    }

    /// Emits a pinned sandbox guard. A violated guard leaves the MIR CFG through executor abort
    /// management, so it has neither a source-error successor nor a guest-cleanup edge.
    fn emit_runtime_check(&mut self, span: Location, call_depth: bool) {
        let check = if call_depth {
            Operation::check_call_depth(span)
        } else {
            Operation::check_fuel(span)
        };
        self.insert(check);
    }

    /// Emits a call to `callee` in value position: the result out-pointer — `destination`, or
    /// throwaway storage (allocated per `ty`'s result convention) when the call is discarded — is
    /// appended as the trailing argument and the call is emitted via
    /// [`emit_call`](Self::emit_call).
    fn emit_call_into(
        &mut self,
        node: &ENode,
        callee: mir::Value,
        mut arguments: Vec<mir::Value>,
        ty: &CallImplType,
        destination: Option<mir::Value>,
        instantiation: Option<Instantiation>,
    ) {
        arguments.push(destination.unwrap_or_else(|| self.allocate_result(node, ty)));
        self.emit_call(node.span, callee, arguments, ty, instantiation);
    }

    /// Emits a call to `callee` in place position: the result storage is allocated per `ty`'s
    /// result convention, appended as the trailing out-pointer argument, and the call is emitted
    /// via [`emit_call`](Self::emit_call). Returns the place of the result: the storage itself for
    /// a value-returning callee, or the loaded place pointer for a place-returning one.
    fn emit_call_as_place(
        &mut self,
        node: &ENode,
        callee: mir::Value,
        mut arguments: Vec<mir::Value>,
        ty: &CallImplType,
        instantiation: Option<Instantiation>,
    ) -> mir::Value {
        let result_storage = self.allocate_result(node, ty);
        arguments.push(result_storage.clone());
        self.emit_call(node.span, callee, arguments, ty, instantiation);
        if ty.returns_place() {
            self.insert(Operation::load(node.span, result_storage))
                .unwrap()
        } else {
            result_storage
        }
    }

    /// Allocates frame storage for every
    /// [`LocalStorage::Owned`](crate::module::function::LocalStorage::Owned) local of the lowered function and
    /// binds it to its `alloca` place.
    ///
    /// Arguments are `NonOwning` and keep their by-value parameter binding. A lowered closure's
    /// captured-environment slots are `Owned` (the body owns the cloned environment) but are *also*
    /// parameters, already bound to their incoming pointers by the parameter loop; they must keep
    /// that binding rather than be re-allocated, so locals already bound (the runtime arguments) are
    /// skipped here. Non-owning, non-argument locals (aliases) are bound to their initializer's place
    /// when their `StoreLocal` is lowered.
    fn allocate_owned_locals(&mut self) {
        let f = self
            .env
            .current
            .get_function_by_id(self.context.source)
            .unwrap();
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
    fn value_dictionary(&self, ty: Type) -> Option<mir::Value> {
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
        type_has_static_layout(ty, self.context.span, &self.env)
    }

    /// Inserts an allocation of storage for an instance of `ty` and returns its address.
    ///
    /// Statically sized storage is allocated directly; storage whose size depends on a generic type
    /// variable carries the `Value` dictionary witnessing its run-time layout as operand.
    fn alloca_storage(&mut self, span: Location, ty: Type) -> mir::Value {
        if self.is_statically_sized(ty) {
            self.insert(Operation::alloca(span, ty)).unwrap()
        } else {
            let witness = self.value_dictionary(ty).unwrap_or_else(|| {
                panic!(
                    "no Value dictionary witnesses the layout of generic storage of type {}",
                    self.show(ty)
                )
            });
            self.insert(Operation::alloca_dynamic(span, ty, witness))
                .unwrap()
        }
    }

    /// Asserts that `ty` has a statically known layout, so that a value of that type may be moved
    /// with direct `load`/`store` operations.
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
            .env
            .current
            .get_function_by_id(self.context.source)
            .unwrap()
            .locals[l.as_index()]
    }

    /// Returns the place (a pointer MIR value) backing the local `l`.
    ///
    /// Every local is bound to a place: an incoming by-pointer parameter or an `Owned` `alloca`
    /// or a non-owned alias.
    fn place_of_local(&self, l: LocalDeclId) -> mir::Value {
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
        destination: Option<mir::Value>,
    ) {
        let d = destination.unwrap_or_else(|| self.alloca_storage(node.span, node.ty));
        if fields.is_empty() {
            // A zero-field aggregate (an empty `struct`/record) has no field store to mark its
            // storage live, so the interpreter could not tell a constructed value from
            // uninitialized storage (both have an empty run-time shape) and would skip its
            // `Value::drop`. Store an empty-tuple literal explicitly — mirroring the HIR
            // interpreter's `build record {}`, which yields and stores a live empty aggregate.
            let empty = self.immediate_constant(node.ty, LiteralValue::new_tuple(vec![]));
            self.store(node.span, empty, d);
            return;
        }
        for (i, n) in fields.iter().enumerate() {
            let field = &self.hir_arena[*n];
            let index = self.int_constant(i as isize);
            let f = self
                .insert(Operation::subfield(field.span, d.clone(), index, field.ty))
                .unwrap();
            self.lower_value_into(field, Some(f));
        }
    }

    /// Lowers an array literal `[e0, e1, …]` into `destination`.
    ///
    /// Mirrors the interpreter's `array_value_from_vec` (`std::array_type`): an `array<A>` is the
    /// record `{ capacity, data, len, start }` whose `data` is a heap `Buffer<A>`. For a statically
    /// `TrivialCopy` element type, `build_array` keeps that construction explicit in MIR so
    /// dataflow can retain the aggregate value. Other element types use the same std primitives the
    /// `.fer` array methods use: `buffer_with_capacity` allocates the backing storage, and each
    /// element is lowered in place into the slot yielded by `buffer_slot` (no temporary, no copy).
    fn lower_array_into(
        &mut self,
        node: &ENode,
        ids: &[hir::ENodeId],
        destination: Option<mir::Value>,
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
        // the field list are cloned out of their type-universe read guards before any operation
        // is emitted: interning a new type takes a write lock, which would deadlock against a still
        // held read guard.
        let named = node
            .ty
            .data()
            .as_named()
            .cloned()
            .expect("an array literal must have a named array type");
        let element_ty = named.params[0];

        // `build_array` reads each operand by representation copy. That needs no `Value<A>`
        // dictionary exactly when A is statically `TrivialCopy`; for an unresolved or resource
        // element type, retain the in-place path below. Each expression is lowered left-to-right
        // to a place before the constructor runs, preserving source evaluation order.
        if concrete_type_is_trivial_copy(element_ty, &self.env) {
            let elements = ids
                .iter()
                .map(|id| self.lower_as_place(&self.hir_arena[*id]))
                .collect::<Vec<_>>();
            self.insert(Operation::build_array(span, element_ty, elements, dest));
            return;
        }

        let shape = named.instantiated_shape(&self.env);
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
        let data_index_value = self.int_constant(data_index as isize);
        let data_place = self
            .insert(Operation::subfield(
                span,
                dest.clone(),
                data_index_value,
                fields[data_index].1,
            ))
            .unwrap();
        let with_capacity = mir::Value::Function(self.demand_std_function("buffer_with_capacity"));
        let capacity_arg = self.int_constant_place(span, len as isize);
        self.insert(Operation::call(
            span,
            with_capacity,
            [capacity_arg, data_place.clone()],
            CallImplType::value(FnType::new_by_val(
                [crate::std::math::int_type()],
                fields[data_index].1,
                no_effects(),
            )),
        ));

        // Fill each slot in place: `buffer_slot(data, i)` yields the slot's place (an
        // `AddressorPlace` return), into which element `i` is lowered directly.
        if len > 0 {
            let buffer_slot =
                mir::Value::Function(self.demand_std_subscript_mut_member("buffer_slot"));
            for (i, id) in ids.iter().enumerate() {
                let index_arg = self.int_constant_place(span, i as isize);
                let slot_out = self
                    .insert(Operation::alloca_place(span, element_ty))
                    .unwrap();
                self.insert(Operation::call(
                    span,
                    buffer_slot.clone(),
                    [data_place.clone(), index_arg, slot_out.clone()],
                    CallImplType::new(
                        FnType::new_mut_resolved(
                            [
                                (fields[data_index].1, true),
                                (crate::std::math::int_type(), false),
                            ],
                            element_ty,
                            no_effects(),
                        ),
                        CallResultConvention::ADDRESSOR_PLACE,
                    ),
                ));
                let slot = self.insert(Operation::load(span, slot_out)).unwrap();
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

    /// Returns the `FunctionId` of the std-library function named `name`. Used to synthesize
    /// calls to std primitives (e.g. the `buffer_*` intrinsics) that the lowered source need not
    /// itself import.
    fn demand_std_function(&self, name: &str) -> FunctionId {
        let std_module = self
            .env
            .module_by_id(STD_MODULE_ID)
            .expect("std module is unavailable during MIR lowering");
        let id = std_module
            .get_local_function_id(Ustr::from(name))
            .unwrap_or_else(|| panic!("std function `{name}` not found"));
        self.demand_function(id, STD_MODULE_ID)
    }

    /// Returns the `FunctionId` of the mutable member of the std-library addressor
    /// subscript named `name`. Used to synthesize slot-place calls (e.g. `buffer_slot`), which are
    /// registered as subscripts rather than plain functions.
    fn demand_std_subscript_mut_member(&self, name: &str) -> FunctionId {
        let std_module = self
            .env
            .module_by_id(STD_MODULE_ID)
            .expect("std module is unavailable during MIR lowering");
        let subscript = std_module
            .get_subscript(Ustr::from(name))
            .unwrap_or_else(|| panic!("std subscript `{name}` not found"));
        let member = subscript
            .mut_member
            .as_ref()
            .unwrap_or_else(|| panic!("std subscript `{name}` has no mut member"));
        self.demand_function(member.function, STD_MODULE_ID)
    }

    /// Allocates a fresh `int` slot, stores the constant `value` into it, and returns its place.
    /// Used to materialize the by-pointer integer arguments of synthesized `buffer_*` calls.
    fn int_constant_place(&mut self, span: Location, value: isize) -> mir::Value {
        let place = self
            .insert(Operation::alloca(span, crate::std::math::int_type()))
            .unwrap();
        let value = self.int_constant(value);
        self.insert(Operation::store(span, value, place.clone()));
        place
    }

    /// Interns a typed Ferlium `int` in the function-local constant pool.
    fn int_constant(&mut self, value: isize) -> mir::Value {
        self.immediate_constant(
            crate::std::math::int_type(),
            LiteralValue::new_native(value),
        )
    }

    /// Stores the integer constant `value` into the `index`-th field (of type `ty`) of the record
    /// at `dest`.
    fn store_int_field(
        &mut self,
        span: Location,
        dest: &mir::Value,
        index: usize,
        ty: Type,
        value: isize,
    ) {
        let index = self.int_constant(index as isize);
        let place = self
            .insert(Operation::subfield(span, dest.clone(), index, ty))
            .unwrap();
        let value = self.int_constant(value);
        self.insert(Operation::store(span, value, place));
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
            | K::Project(_)
            | K::GetDictionaryFunction(_)
            | K::WithPlace(_) => true,
            K::FunctionApply(n) => n.ty.returns_place(),
            K::StaticApply(n) => n.ty.returns_place(),
            K::SubscriptApply(n) => n.ty.returns_place(),
            K::CallDictionaryFunction(n) => n.ty.returns_place(),
            // A non-trivial clone consumed as a place is elided in favor of its source's place
            // (mirroring `try_eval_node_as_place`): the consumer — a store-with-clone or an
            // enclosing clone — performs the single copy itself.
            K::CloneValue(n) => {
                matches!(
                    n.clone,
                    ResolvedLocalClone::Static(_) | ResolvedLocalClone::Dictionary(_)
                ) && self.node_yields_place(&self.hir_arena[n.source])
            }
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
    fn lower_as_place(&mut self, node: &ENode) -> mir::Value {
        use hir::NodeKind as K;
        match &node.kind {
            K::LoadLocal(n) => self.place_of_local(n.id),

            K::LoadDictionary(n) => {
                // A dictionary parameter is already a place.
                self.context.extra_parameters[&n.extra_parameter].clone()
            }

            K::CloneValue(n)
                if matches!(
                    n.clone,
                    ResolvedLocalClone::Static(_) | ResolvedLocalClone::Dictionary(_)
                ) && self.node_yields_place(&self.hir_arena[n.source]) =>
            {
                // A non-trivial clone consumed as a place: forward the source's place, eliding
                // this clone (mirroring `try_eval_node_as_place`'s `CloneValue` arm). The
                // consumer — a store-with-clone or an enclosing clone — performs the single copy.
                self.lower_as_place(&self.hir_arena[n.source])
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
                    self.insert(Operation::dict_entry(
                        node.span,
                        dict,
                        TraitDictionaryEntryIndex::from_index(n.index.as_index()),
                        node.ty,
                    ))
                    .unwrap()
                } else {
                    let base = self.lower_as_place(base_node);
                    let index = self.int_constant(n.index.as_index() as isize);
                    self.insert(Operation::subfield(node.span, base, index, node.ty))
                        .unwrap()
                }
            }

            K::FunctionApply(n) => {
                // The callee is lowered as a *place*: a function value (in particular a closure) is
                // borrowed in place and read by reference at the call, so it survives repeated calls
                // (`f() + f()`) and is dropped once by its scope cleanup — mirroring the HIR
                // interpreter's `eval_apply`, which calls through a borrow of the function value.
                let f = self.lower_as_place(&self.hir_arena[n.function]);
                let arguments: Vec<mir::Value> = n
                    .arguments
                    .iter()
                    .map(|arg| self.lower_argument(arg))
                    .collect();
                self.emit_call_as_place(node, f, arguments, &n.ty, None)
            }

            K::StaticApply(n) => {
                let f = self.function_value(n.function);
                let mut arguments: Vec<mir::Value> = vec![];
                for x in &n.extra_arguments {
                    arguments.push(self.lower_extra_argument(&self.hir_arena[*x]));
                }
                for arg in &n.arguments {
                    arguments.push(self.lower_as_place(&self.hir_arena[arg.value]));
                }
                self.emit_call_as_place(
                    node,
                    f,
                    arguments,
                    &n.ty,
                    Self::instantiation_of(&n.inst_data),
                )
            }

            K::SubscriptApply(n) => {
                // A place-returning subscript application (an addressor member): resolve the
                // member out of the subscript evidence, then call it like any other place call.
                // The member function value carries the subscript's captured hidden evidence, so
                // no extra arguments are passed here.
                let f = self.lower_subscript_member(node, n);
                let arguments: Vec<mir::Value> = n
                    .arguments
                    .iter()
                    .map(|arg| self.lower_argument(arg))
                    .collect();
                self.emit_call_as_place(node, f, arguments, &n.ty, None)
            }

            K::CallDictionaryFunction(n) => {
                // A place-returning method dispatched through a dictionary: project+load the
                // method, call it with a place out-pointer, then load the returned place.
                let (function, arguments) = self.lower_dictionary_function_target(node, n);
                self.emit_call_as_place(node, function, arguments, &n.ty, None)
            }

            K::GetDictionaryFunction(n) => {
                // A trait function taken as a first-class value through a (generic) dictionary: the
                // symbolic analog of projecting the function out of the witness table. `dict_entry`
                // yields the place of the bare function value, which the consumer reads
                // by reference at the call — exactly like a `project`ed method slot.
                let dictionary = self.lower_dictionary_operand(&self.hir_arena[n.dictionary]);
                self.insert(Operation::dict_entry(
                    node.span,
                    dictionary,
                    n.entry_index,
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
        // Unwrap block accessors: lower their leading statements now and defer their cleanup
        // locals into the projection scope, so they are dropped after the accessor slide runs
        // (mirroring `eval_block_accessor_until_yield`, which pushes the block cleanup onto the
        // epilogue). Nested blocks defer outermost-first; the scope's reverse-order exit then
        // drops innermost-first.
        let mut accessor = &self.hir_arena[n.accessor];
        let mut deferred_cleanup: Vec<LocalDeclId> = vec![];
        while let hir::NodeKind::Block(block) = &accessor.kind {
            let (tail, prefix) = block
                .body
                .split_last()
                .expect("a WithYielded accessor block must contain an accessor call");
            for s in prefix {
                if self.current_block_is_terminated() {
                    break;
                }
                self.lower_value_into(&self.hir_arena[*s], None);
            }
            deferred_cleanup.extend(block.cleanup.iter().copied());
            accessor = &self.hir_arena[*tail];
        }

        // Dead code: a leading statement terminated the block, so the accessor is never entered.
        // Bind the binding to an arbitrary valid place (never consumed) and push the scope the
        // caller's `exit_scope` expects; its cleanup no-ops on the terminated path.
        if self.current_block_is_terminated() {
            let dummy = self.context.return_destination.clone();
            self.context.locals.insert(n.binding, dummy.clone());
            self.context.scopes.push(Scope {
                actions: Vec::new(),
                pad: None,
            });
            return;
        }

        let (callee, extra_arguments, visible_arguments, call_ty) = match &accessor.kind {
            // A statically known member: a constant function callee plus its evidence arguments.
            hir::NodeKind::StaticApply(app) => (
                self.function_value(app.function),
                &app.extra_arguments[..],
                &app.arguments,
                app.ty.clone(),
            ),
            // A member applied through subscript evidence: the resolved member function value
            // carries the subscript's captured hidden evidence itself, so no extra arguments.
            hir::NodeKind::SubscriptApply(app) => (
                self.lower_subscript_member(accessor, app),
                &[][..],
                &app.arguments,
                app.ty.clone(),
            ),
            other => panic!(
                "a WithYielded accessor must be a StaticApply or SubscriptApply of a YieldedOnce member, got {other:?}"
            ),
        };
        let mut arguments: Vec<mir::Value> = vec![];
        for x in extra_arguments {
            arguments.push(self.lower_extra_argument(&self.hir_arena[*x]));
        }
        for arg in visible_arguments {
            arguments.push(self.lower_as_place(&self.hir_arena[arg.value]));
        }
        // Accessor-expression temporaries are already live while the ramp runs. Give `project` an
        // error pad that drops them if the ramp fails. On success this scope is promoted below to
        // the projection scope, where the same temporaries remain live until after the slide.
        self.enter_scope(&deferred_cleanup);
        // The exposed place's pointee type is the binding's (element) type. `project` runs the ramp
        // to the yield and binds the yielded place to its result register.
        //
        // A fallible `project` becomes an `invoke` whose explicit error successor drops the
        // caller's live temporaries before propagating.
        let element_ty = self.local_declaration(n.binding).ty;
        let place = self
            .insert(Operation::project(
                accessor.span,
                callee,
                arguments,
                element_ty,
                call_ty.clone(),
            ))
            .unwrap();
        self.context.locals.insert(n.binding, place.clone());
        let scope = self
            .context
            .scopes
            .last_mut()
            .expect("the accessor-ramp temporary scope must be active");
        scope.push_action(CleanupAction::EndProject { place, call_ty });
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
    /// An immediate stays a typed opaque constant; everything else is taken as its **place** (a
    /// borrow), never loaded/moved. This mirrors the HIR interpreter's `eval_case`, which reads the
    /// scrutinee through `target_ref` and compares its `to_literal_value()`: the place stays live for
    /// the remaining alternatives and for the arm body (so a non-trivial scrutinee — string/tuple —
    /// is not consumed), and a bare-generic scrutinee needs no static-layout assertion because it is
    /// only borrowed and snapshotted, not loaded as a register. (A variant scrutinee arrives as the
    /// `int` `extract_tag`, materialized into a place here.)
    fn lower_case_scrutinee(&mut self, node: &ENode) -> mir::Value {
        use hir::NodeKind as K;
        if let K::Immediate(value) = &node.kind {
            return self.immediate_constant(node.ty, value.clone());
        }
        self.lower_as_place(node)
    }

    /// Lowers compile-time pattern data to an operand for `comp_eq`. Pattern values deliberately do
    /// not enter the HIR-immediate constant pool: they are matcher metadata, not runtime constants.
    fn lower_case_pattern(&mut self, pattern: &LiteralValue) -> mir::Value {
        mir::Value::Pattern(containers::b(pattern.clone()))
    }

    /// Lowers `arg` to its call operand: a pointer to the argument's storage.
    ///
    /// All arguments are represented indirectly in MIR.
    fn lower_argument(&mut self, arg: &CallArgument<Elaborated>) -> mir::Value {
        self.lower_as_place(&self.hir_arena[arg.value])
    }

    /// Returns the blocks created for `n`.
    fn create_case_blocks(&mut self, n: &Case<Elaborated>) -> CaseBlocks {
        let mut heads: Vec<BlockId> = vec![];
        let mut bodies: Vec<BlockId> = vec![];
        for _ in n.alternatives.iter() {
            heads.push(self.context.function.add_block());
            bodies.push(self.context.function.add_block());
        }
        let default: BlockId = self.context.function.add_block();
        let tail: BlockId = self.context.function.add_block();
        CaseBlocks {
            heads,
            bodies,
            default,
            tail,
        }
    }

    /// Returns the symbolic MIR dictionary lowered from `n`: the canonical interned handle of the
    /// impl that satisfies it. The dictionary is kept symbolic (not materialized into a witness-table
    /// tuple); the MIR interpreter dispatches through the interned id, and a future
    /// tuple-lowering pass rebuilds the table from the impl arena.
    fn lower_dictionary(&mut self, n: &GetDictionary) -> mir::Value {
        mir::Value::Dictionary(self.dictionary_id(n.dictionary))
    }

    /// Lowers a HIR dictionary node to a symbolic MIR dictionary operand.
    ///
    /// A static `GetDictionary` becomes a `Dictionary(id)` constant; a forwarded `LoadDictionary`
    /// becomes the `@extra` parameter slot it arrives in (a `Parameter`). The dictionary is never
    /// materialized into a witness-table tuple. (Dictionary entries are only methods and associated
    /// consts — `TraitDictionaryEntry` has no nested-dictionary variant — so a dictionary operand is
    /// always one of these two node kinds.)
    fn lower_dictionary_operand(&self, node: &ENode) -> mir::Value {
        use hir::NodeKind as K;
        match &node.kind {
            K::GetDictionary(d) => mir::Value::Dictionary(self.dictionary_id(d.dictionary)),
            K::LoadDictionary(n) => self.context.extra_parameters[&n.extra_parameter].clone(),
            other => panic!("expected a trait dictionary node, got {:?}", other),
        }
    }

    /// Lowers a HIR subscript-evidence node to a symbolic MIR subscript operand.
    ///
    /// A static `GetSubscript` becomes a `Subscript(id)` constant; a forwarded
    /// `LoadSubscriptEvidence` becomes the `@extra` parameter slot it arrives in (a `Parameter`);
    /// any other node (e.g. a first-class subscript value bound to a local) is the place of the
    /// subscript value, read non-consumingly (mirroring `eval_subscript_value`). Like a
    /// dictionary, the subscript is never materialized into a member-table value here.
    fn lower_subscript_operand(&mut self, node: &ENode) -> mir::Value {
        use hir::NodeKind as K;
        match &node.kind {
            K::GetSubscript(n) => mir::Value::Subscript(n.subscript),
            K::LoadSubscriptEvidence(n) => {
                self.context.extra_parameters[&n.extra_parameter].clone()
            }
            _ => self.lower_as_place(node),
        }
    }

    /// Lowers the callee of a subscript application: resolves the applied `ref`/`mut` member out of
    /// the symbolic subscript evidence with `subscript_member`, yielding the place of the member
    /// function value (which bundles the subscript's captured hidden evidence, so the `call`/
    /// `project` consuming it prepends that evidence exactly as for a closure).
    fn lower_subscript_member(
        &mut self,
        node: &ENode,
        n: &hir::SubscriptApplication<Elaborated>,
    ) -> mir::Value {
        let subscript = self.lower_subscript_operand(&self.hir_arena[n.subscript]);
        let member_ty = Type::function_type(n.ty.fn_ty.clone());
        self.insert(Operation::subscript_member(
            node.span,
            subscript,
            n.mut_member,
            member_ty,
        ))
        .unwrap()
    }

    /// Lowers a call's extra (evidence) argument to its MIR operand: a trait dictionary becomes a
    /// symbolic dictionary operand (`lower_dictionary_operand`), subscript evidence a symbolic
    /// subscript operand (`lower_subscript_operand`), while any other evidence is lowered as a
    /// place.
    fn lower_extra_argument(&mut self, node: &ENode) -> mir::Value {
        use hir::NodeKind as K;
        match &node.kind {
            K::GetDictionary(_) | K::LoadDictionary(_) => self.lower_dictionary_operand(node),
            K::GetSubscript(_) | K::LoadSubscriptEvidence(_) => self.lower_subscript_operand(node),
            K::LoadVariantPayloadStorageEvidence(n) => {
                self.context.extra_parameters[&n.extra_parameter].clone()
            }
            _ => self.lower_as_place(node),
        }
    }

    /// Stores the register `value` into `dest` if a destination is present; a `None` `dest`
    /// discards the value.
    fn store_into_if_needed(
        &mut self,
        span: Location,
        value: mir::Value,
        destination: Option<mir::Value>,
    ) {
        if let Some(d) = destination {
            self.insert(Operation::store(span, value, d));
        }
    }

    /// Inserts a `store` operation to store `v` at `destination`.
    fn store(&mut self, span: Location, v: mir::Value, destination: mir::Value) {
        self.insert(Operation::store(span, v, destination));
    }

    /// Writes `()` into the result slot of a `()`-yielding tail (an assignment, a `let`, a closure-env
    /// drop) that produces no value itself, so a `()`-returning body ending in one still initializes
    /// its (husk) `@ret`. A no-op for a `None` destination (statement position) or a terminated block.
    fn store_unit_result(&mut self, span: Location, destination: Option<mir::Value>) {
        if !self.current_block_is_terminated() {
            let unit = self.immediate_constant(Type::unit(), LiteralValue::new_native(()));
            self.store_into_if_needed(span, unit, destination);
        }
    }

    /// Copies the pointee of the place `source` into `destination` as a single `memcpy` (the fused
    /// form of a `load` immediately followed by a `store` of the loaded value). A `None`
    /// `destination` discards the copy.
    fn memcpy_into_if_needed(
        &mut self,
        span: Location,
        source: mir::Value,
        destination: Option<mir::Value>,
    ) {
        if let Some(d) = destination {
            self.insert(Operation::memcpy(span, source, d));
        }
    }

    /// Moves the whole pointee of `source` into `destination`, choosing a plain `move` for a
    /// statically-sized value or a witnessed `move_dynamic` for a generic (dynamically-sized) one.
    ///
    /// Unlike a *copy*, a move transfers ownership wholesale and needs no `Value::clone`; a generic
    /// move is therefore a byte-move whose size the witness supplies (the interpreter moves the value
    /// shape-agnostically and ignores the witness).
    fn move_value_into(
        &mut self,
        span: Location,
        source: mir::Value,
        destination: mir::Value,
        ty: Type,
    ) {
        if self.is_statically_sized(ty) {
            self.insert(Operation::move_value(span, source, destination));
        } else {
            let witness = self.value_dictionary(ty).unwrap_or_else(|| {
                panic!(
                    "no Value dictionary witnesses the layout of the generic value of type {} moved out",
                    self.show(ty)
                )
            });
            self.insert(Operation::move_dynamic(span, source, destination, witness));
        }
    }

    /// Projects the function reference out of `n`'s dictionary place and lowers the call's runtime
    /// arguments to their place operands. Returns `(function, arguments)` ready
    /// to be completed with a result out-pointer and emitted as a `call`.
    fn lower_dictionary_function_target(
        &mut self,
        node: &ENode,
        n: &hir::CallDictionaryFunction<Elaborated>,
    ) -> (mir::Value, Vec<mir::Value>) {
        let dictionary = self.lower_dictionary_operand(&self.hir_arena[n.dictionary]);
        let function_ty = Type::function_type(n.ty.fn_ty.clone());
        // The callee is the place of the function entry; the call reads the function value by
        // reference rather than loading it into a register (see the `call` contract).
        let function_place = self
            .insert(Operation::dict_entry(
                node.span,
                dictionary,
                n.entry_index,
                function_ty,
            ))
            .unwrap();
        let arguments = n.arguments.iter().map(|a| self.lower_argument(a)).collect();
        (function_place, arguments)
    }

    /// Inserts an allocation of the result storage for a call to a function of type `f` and returns
    /// its address. `node` supplies the span and the concrete result type for the allocation.
    ///
    /// The allocation depends on `f`'s result convention:
    /// - [`CallResultConvention::Value`] allocates storage for the returned value (`alloca`) — including
    ///   a unit return, which allocates a (zero-sized) `()` cell the callee initializes with the live
    ///   unit value, so every result, unit or not, flows through a real cell;
    /// - [`SubscriptResultConvention::AddressorPlace`] allocates a slot holding the returned place
    ///   pointer (`alloca_place`).
    ///
    /// [`SubscriptResultConvention::YieldedOnce`] is never reached here: a yielded member is entered
    /// with a `project` (which exposes the yielded place as its own result register), never called
    /// for a result through this helper.
    fn allocate_result(&mut self, node: &ENode, f: &CallImplType) -> mir::Value {
        match f.result_convention {
            CallResultConvention::Value => self.alloca_storage(node.span, node.ty),
            CallResultConvention::Subscript(SubscriptResultConvention::AddressorPlace) => self
                .insert(Operation::alloca_place(node.span, node.ty))
                .unwrap(),
            CallResultConvention::Subscript(SubscriptResultConvention::YieldedOnce) => {
                panic!("a YieldedOnce member is entered via `project`, never called for a result")
            }
        }
    }

    /// Lowers a place-returning call in value position: the call's place result is resolved and
    /// its value is copied into the destination (trivial copy; non-trivial reads are wrapped in
    /// `CloneValue` by HIR). A `None` destination lowers the call for its effects only.
    fn lower_place_call_into(&mut self, node: &ENode, destination: Option<mir::Value>) {
        let place = self.lower_as_place(node);
        if destination.is_some() {
            self.assert_statically_sized(node.ty);
            self.memcpy_into_if_needed(node.span, place, destination);
        }
    }

    /// Lowers `node` in destination-passing style: the value produced by `node` is stored into the
    /// storage pointed to by `dest`. A `None` `dest` denotes a discarded result (effects only); a
    /// `()`-typed node also has nothing to store.
    fn lower_value_into(&mut self, node: &ENode, destination: Option<mir::Value>) {
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
                // structurally, so the MIR does the same.)
                let scrutinee = self.lower_case_scrutinee(&self.hir_arena[n.value]);

                // With no alternatives (e.g. a single irrefutable arm), there are no condition
                // heads to test, so branch straight to the default block.
                let entry = blocks.heads.first().copied().unwrap_or(blocks.default);
                self.terminate(Terminator::goto(node.span, entry));

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
                        .insert(Operation::compare_eq(node.span, scrutinee.clone(), pattern))
                        .unwrap();
                    self.terminate(Terminator::cond_br(node.span, eq, blocks.bodies[i], next));

                    // Lower the body of the alternative into the destination. A `break`/`continue`/
                    // `return` arm terminates its own block, so it needs no branch to the tail.
                    self.context.point = InsertionPoint::End(blocks.bodies[i]);
                    self.lower_value_into(&self.hir_arena[*a], destination.clone());
                    if !self.current_block_is_terminated() {
                        self.terminate(Terminator::goto(node.span, blocks.tail));
                    }
                }

                // Default case.
                self.context.point = InsertionPoint::End(blocks.default);
                self.lower_value_into(&self.hir_arena[n.default], destination.clone());
                if !self.current_block_is_terminated() {
                    self.terminate(Terminator::goto(node.span, blocks.tail));
                }

                // Tail. The value has already been stored into `dest`.
                self.context.point = InsertionPoint::End(blocks.tail);
            }

            K::Immediate(n) => {
                let value = self.immediate_constant(node.ty, n.clone());
                self.store_into_if_needed(node.span, value, destination);
            }

            K::Assign(n) => {
                // Mirror the interpreter's `eval_assign` ordering: evaluate the right-hand side,
                // then drop the destination's previous value, then store the new one.
                //
                // The right-hand side may read any part of the destination it overwrites. It must be
                // completed in fresh storage even when the old value needs no semantic drop: direct
                // field-by-field aggregate construction could otherwise overwrite an early field
                // before a later field reads it (for example `a = (a.1, a.0)`). A later MIR
                // optimization may elide this temporary after proving non-aliasing.
                let place = self.lower_as_place(&self.hir_arena[n.place]);
                let dropped_ty = self.hir_arena[n.place].ty;
                let value_span = self.hir_arena[n.value].span;
                let value_ty = self.hir_arena[n.value].ty;
                let temp = self.alloca_storage(value_span, value_ty);
                self.lower_value_into(&self.hir_arena[n.value], Some(temp.clone()));
                if self.current_block_is_terminated() {
                    return;
                }
                if let Some(spec) = n.drop.and_then(|drop| self.resolve_drop(drop)) {
                    self.emit_drop(node.span, place.clone(), dropped_ty, spec);
                }
                // The fresh temporary is consumed, not copied. A move is shape-agnostic, so it
                // works for a generic `value_ty` too; `move_value_into` carries a run-time layout
                // witness when the type is not statically sized.
                self.move_value_into(node.span, temp, place, value_ty);
                // `Assign` yields `()`; in value/tail position initialize the destination slot.
                self.store_unit_result(node.span, destination);
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
                        let clone = ResolvedLocalClone::Static(f);
                        let f = self.function_value(f);

                        let target = self.place_of_local(n.id);
                        let source_node = &self.hir_arena[n.value];
                        let (source, temp_drop) = self.lower_clone_source(&clone, source_node);

                        self.insert(Operation::clone_value(
                            node.span,
                            source.clone(),
                            target,
                            f,
                            self.local_declaration(n.id).ty,
                        ));
                        if let Some(spec) = temp_drop {
                            self.emit_drop(node.span, source, source_node.ty, spec);
                        }
                    }
                    Some(ResolvedLocalClone::Dictionary(dictionary)) => {
                        // Clone the source place into the local's (uninitialized) owned storage
                        // through the `Value::clone` method loaded from the dictionary parameter.
                        let cloned_ty = self.local_declaration(n.id).ty;
                        let target = self.place_of_local(n.id);
                        let source_node = &self.hir_arena[n.value];
                        let (source, temp_drop) = self.lower_clone_source(
                            &ResolvedLocalClone::Dictionary(dictionary),
                            source_node,
                        );
                        self.lower_value_clone_via_dictionary(
                            node.span,
                            dictionary,
                            cloned_ty,
                            source.clone(),
                            target,
                        );
                        if let Some(spec) = temp_drop {
                            self.emit_drop(node.span, source, source_node.ty, spec);
                        }
                    }
                }
                // `StoreLocal` yields `()`; in value/tail position initialize the destination slot.
                self.store_unit_result(node.span, destination);
            }

            K::CloneValue(n) => {
                match n.clone {
                    // A trivial copy: load the source place and store it into the destination. A later
                    // ABI pass may relax this to direct passing where physically possible.
                    ResolvedLocalClone::TrivialCopy => {
                        self.lower_value_into(&self.hir_arena[n.source], destination);
                    }
                    ResolvedLocalClone::Static(f) => {
                        // Clone the source place into the destination through the statically known
                        // clone function `f`. A `None` destination still needs target storage to
                        // clone into (as in the `Dictionary` arm below).
                        let clone = ResolvedLocalClone::Static(f);
                        let f = self.function_value(f);

                        let target =
                            destination.unwrap_or_else(|| self.alloca_storage(node.span, node.ty));
                        let source_node = &self.hir_arena[n.source];
                        let (source, temp_drop) = self.lower_clone_source(&clone, source_node);

                        self.insert(Operation::clone_value(
                            node.span,
                            source.clone(),
                            target,
                            f,
                            node.ty,
                        ));
                        if let Some(spec) = temp_drop {
                            self.emit_drop(node.span, source, source_node.ty, spec);
                        }
                    }
                    ResolvedLocalClone::Dictionary(dictionary) => {
                        // Materialize an owned snapshot by cloning the source place into a fresh
                        // target through the `Value::clone` method loaded from the dictionary
                        // parameter. A `None` destination still needs target storage to clone into.
                        let target =
                            destination.unwrap_or_else(|| self.alloca_storage(node.span, node.ty));
                        let source_node = &self.hir_arena[n.source];
                        let (source, temp_drop) = self.lower_clone_source(
                            &ResolvedLocalClone::Dictionary(dictionary),
                            source_node,
                        );
                        self.lower_value_clone_via_dictionary(
                            node.span,
                            dictionary,
                            node.ty,
                            source.clone(),
                            target,
                        );
                        if let Some(spec) = temp_drop {
                            self.emit_drop(node.span, source, source_node.ty, spec);
                        }
                    }
                }
            }

            K::TakeLocalValue(n) => match n.mode {
                ResolvedTakeLocalValueMode::MoveOwned => {
                    // Move the owned value out: transfer the place into the destination, skipping the
                    // local's lexical drop (cleanup is deferred). A move transfers the value
                    // wholesale, so a generic (dynamically-sized) value needs no `Value::clone` —
                    // just a witnessed `move_dynamic`; a statically-sized one uses a plain `move`.
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
                                let f = self.function_value(f);
                                let source = self.place_of_local(n.id);
                                self.insert(Operation::clone_value(
                                    node.span,
                                    source,
                                    destination,
                                    f,
                                    node.ty,
                                ));
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
                let f = self.function_value(n.function);
                let mut arguments: Vec<mir::Value> = vec![];
                for x in &n.extra_arguments {
                    arguments.push(self.lower_extra_argument(&self.hir_arena[*x]));
                }
                for arg in &n.arguments {
                    arguments.push(self.lower_argument(arg));
                }

                assert_eq!(node.ty, n.ty.ret());
                self.emit_call_into(
                    node,
                    f,
                    arguments,
                    &n.ty,
                    destination,
                    Self::instantiation_of(&n.inst_data),
                );
            }

            K::GetDictionary(d) => {
                let dict = self.lower_dictionary(d);
                self.store_into_if_needed(node.span, dict, destination);
            }

            K::GetSubscript(n) => {
                // A first-class reference to a statically known subscript: a symbolic constant,
                // stored into the destination exactly like a dictionary.
                let subscript = mir::Value::Subscript(n.subscript);
                self.store_into_if_needed(node.span, subscript, destination);
            }

            K::BuildSubscriptValue(n) => {
                // Bundle the base subscript with captured hidden evidence into a first-class
                // subscript value (mirroring `eval_build_subscript_value`).
                let base = self.lower_subscript_operand(&self.hir_arena[n.subscript]);
                let evidence: Vec<mir::Value> = n
                    .evidence_captures
                    .iter()
                    .map(|e| self.lower_extra_argument(&self.hir_arena[*e]))
                    .collect();
                let value = self
                    .insert(Operation::build_subscript(
                        node.span, base, evidence, node.ty,
                    ))
                    .unwrap();
                self.store_into_if_needed(node.span, value, destination);
            }

            K::CloneSubscriptValue(n) => {
                // Clone a first-class subscript value: read the source (non-consumingly) into a
                // fresh value — a capture-less `build_subscript` (mirroring
                // `eval_clone_subscript_value`, which snapshots the source's subscript value).
                let source = self.lower_subscript_operand(&self.hir_arena[n.source]);
                let value = self
                    .insert(Operation::build_subscript(
                        node.span,
                        source,
                        vec![],
                        node.ty,
                    ))
                    .unwrap();
                self.store_into_if_needed(node.span, value, destination);
            }

            K::DropSubscriptValue(n) => {
                // Drop a first-class subscript value: it carries only interned evidence (no user
                // resource), so no semantic operation is emitted (mirroring
                // `eval_drop_subscript_value`). The target place is still lowered for effects.
                let _ = self.lower_as_place(&self.hir_arena[n.target]);
                self.store_unit_result(node.span, destination);
            }

            K::SubscriptApply(n) => {
                if n.ty.returns_place() {
                    return self.lower_place_call_into(node, destination);
                }
                // Resolve the applied member out of the subscript evidence; the member function
                // value carries the subscript's captured hidden evidence, so the call passes only
                // the visible arguments (plus the result out-pointer).
                let f = self.lower_subscript_member(node, n);
                let arguments: Vec<mir::Value> = n
                    .arguments
                    .iter()
                    .map(|arg| self.lower_argument(arg))
                    .collect();
                self.emit_call_into(node, f, arguments, &n.ty, destination, None);
            }

            K::GetFunction(n) => {
                // A first-class reference to a (non-generic) function: lower to a constant function
                // value and store it into the destination. A generic function used first-class is
                // wrapped by elaboration in a `BuildClosure` carrying its dictionary captures, so a
                // bare `GetFunction` never needs evidence here.
                let f = self.function_value(n.function);
                self.store_into_if_needed(node.span, f, destination);
            }

            K::BuildClosure(n) => {
                // Build a first-class closure value bundling the target function with its captured
                // environment. The target's body receives, as leading by-pointer parameters, first
                // its hidden `@extra` dictionaries and then the value captures; the closure carries
                // both and the MIR `call` prepends them at every application (see the interpreter).
                //
                // Hidden dictionary captures and the environment's own `Value` dictionary are kept
                // symbolic (a static `Dictionary(id)` or a forwarded `@extra` parameter), so both
                // statically-resolved and generic-forwarded closures lower uniformly.

                // The hidden dictionary/evidence captures the lambda body needs, in order.
                let hidden_dicts: Vec<mir::Value> = n
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
                // them into its environment. A capture is consumed *by value*, so a clone capture
                // must materialize an owned temporary — the clone-as-place elision of
                // `lower_as_place` applies only to place consumers that copy for themselves.
                let captures: Vec<mir::Value> = n
                    .captures
                    .iter()
                    .map(|c| {
                        let capture = &self.hir_arena[*c];
                        if matches!(capture.kind, hir::NodeKind::CloneValue(_)) {
                            let temp = self.alloca_storage(capture.span, capture.ty);
                            self.lower_value_into(capture, Some(temp.clone()));
                            temp
                        } else {
                            self.lower_as_place(capture)
                        }
                    })
                    .collect();

                let closure = self
                    .insert(Operation::build_closure(
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
                    .insert(Operation::clone_closure_env(node.span, source, node.ty))
                    .unwrap();
                self.store_into_if_needed(node.span, cloned, destination);
            }

            K::DropClosureEnv(n) => {
                // Drop the owned captured environment of the target closure — the body of the
                // generated `Value::drop` for a function type. It yields `()`.
                let target = self.lower_as_place(&self.hir_arena[n.target]);
                self.insert(Operation::drop_closure_env(node.span, target));
                self.store_unit_result(node.span, destination);
            }

            K::FunctionApply(n) => {
                if n.ty.returns_place() {
                    return self.lower_place_call_into(node, destination);
                }
                // The callee is lowered as a *place*: a function value (in particular a closure) is
                // borrowed in place and read by reference at the call, so it survives repeated calls
                // (`f() + f()`) and is dropped once by its scope cleanup — mirroring the HIR
                // interpreter's `eval_apply`, which calls through a borrow of the function value.
                let f = self.lower_as_place(&self.hir_arena[n.function]);
                let arguments: Vec<mir::Value> = n
                    .arguments
                    .iter()
                    .map(|arg| self.lower_argument(arg))
                    .collect();
                self.emit_call_into(node, f, arguments, &n.ty, destination, None);
            }

            K::Project(_) => {
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
                let marker = self.insert(Operation::stack_save(node.span)).unwrap();

                let head = self.context.function.add_block();
                let exit = self.context.function.add_block();
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
                self.terminate(Terminator::goto(node.span, head));
                self.context.point = InsertionPoint::End(head);

                // The body's value is discarded each iteration (the result flows through `break`).
                self.lower_value_into(&self.hir_arena[n.body], None);

                // Back-edge: a body that falls through reclaims its iteration's stack and loops.
                if !self.current_block_is_terminated() {
                    self.insert(Operation::stack_restore(node.span, marker));
                    self.terminate(Terminator::goto(node.span, head));
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
                    self.insert(Operation::stack_restore(node.span, frame.marker));
                    self.terminate(Terminator::goto(node.span, frame.exit));
                }
            }

            K::Continue(n) => {
                // Drop the scopes entered inside the loop, reclaim the iteration's stack, and jump
                // back to the loop head.
                let frame = self.loop_frame(n.label);
                self.emit_unwind_drops(node.span, frame.scope_depth);
                self.insert(Operation::stack_restore(node.span, frame.marker));
                self.terminate(Terminator::goto(node.span, frame.head));
            }

            K::ExtractTag(n) => {
                // Read the variant's tag as an `int`. The operand (typically a `LoadLocal` of the
                // scrutinee) is lowered as the variant's place; `extract_tag` reads its tag without
                // consuming the variant, so the payload remains accessible to the match arms.
                let place = self.lower_as_place(&self.hir_arena[*n]);
                let tag = self
                    .insert(Operation::extract_tag(node.span, place))
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
                let (storage, evidence) = match n
                    .payload_storage
                    .expect("elaborated variant must have payload-storage metadata")
                {
                    hir::VariantPayloadStorageSource::Static(storage) => (Some(storage), None),
                    hir::VariantPayloadStorageSource::Evidence(extra_parameter) => (
                        None,
                        Some(self.context.extra_parameters[&extra_parameter].clone()),
                    ),
                };
                let shell = self
                    .insert(Operation::variant(
                        node.span, n.tag, node.ty, storage, evidence,
                    ))
                    .unwrap();
                self.store(node.span, shell, dest.clone());
                // A case carrying nothing has no payload to write, and writing unit would force the
                // runtime to materialize the payload slot the representation exists to avoid.
                if payload.ty != Type::unit() {
                    let payload_index = self.int_constant(0);
                    let payload_place = self
                        .insert(Operation::subfield(
                            node.span,
                            dest,
                            payload_index,
                            payload.ty,
                        ))
                        .unwrap();
                    self.lower_value_into(payload, Some(payload_place));
                }
            }

            K::LoadDictionary(n) => {
                // A required dictionary/evidence resolves to its incoming extra parameter, which is a
                // place. Copy it into the destination if one is requested.
                if destination.is_some() {
                    let p = self.context.extra_parameters[&n.extra_parameter].clone();
                    self.memcpy_into_if_needed(node.span, p, destination);
                }
            }

            K::LoadSubscriptEvidence(n) => {
                // Forwarded subscript evidence is likewise an incoming by-pointer extra parameter.
                // When it is used as a first-class value rather than only as call metadata, copy
                // that value into the requested destination.
                if destination.is_some() {
                    let p = self.context.extra_parameters[&n.extra_parameter].clone();
                    self.memcpy_into_if_needed(node.span, p, destination);
                }
            }

            K::LoadVariantPayloadStorageEvidence(n) => {
                if destination.is_some() {
                    let p = self.context.extra_parameters[&n.extra_parameter].clone();
                    self.memcpy_into_if_needed(node.span, p, destination);
                }
            }

            K::CallDictionaryFunction(n) => {
                // A place-returning dictionary function is resolved as a place and copied into the destination,
                // like any other place-returning call.
                if n.ty.returns_place() {
                    return self.lower_place_call_into(node, destination);
                }
                // Project the function out of the dictionary, load it, then call it into the
                // destination (or a throwaway result for a discarded call).
                let (function, arguments) = self.lower_dictionary_function_target(node, n);
                self.emit_call_into(node, function, arguments, &n.ty, destination, None);
            }

            K::CheckCallDepth => self.emit_runtime_check(node.span, true),

            K::CheckFuel => self.emit_runtime_check(node.span, false),

            K::Tuple(ns) => self.lower_aggregate_into(node, ns, destination),

            K::Record(ns) => self.lower_aggregate_into(node, ns, destination),

            K::Uninit => {
                self.insert(Operation::clear(
                    node.span,
                    destination.expect("discarded uninit construction is not yet implemented"),
                ));
            }

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

            K::GetDictionaryFunction(_) => {
                // A trait function as a first-class value: take its `dict_entry` place (see
                // `lower_as_place`) and copy the (trivially-copyable, bare) function value into the
                // destination, like reading any other dictionary entry.
                if destination.is_some() {
                    let function_place = self.lower_as_place(node);
                    self.memcpy_into_if_needed(node.span, function_place, destination);
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
                self.terminate(Terminator::ret(node.span));
            }

            K::Yield(place_node) => {
                // Inside a `YieldedOnce` accessor body: expose the yielded place to the driving
                // `project` and suspend. The place flows out through the `yield` (not the return
                // out-pointer), so the ambient `destination` is irrelevant — the accessor is driven
                // with none. Mirrors the HIR interpreter's `eval_yield`. The operations emitted
                // after this (the slide) run only when `end_project` resumes the accessor.
                let place = self.lower_as_place(&self.hir_arena[*place_node]);
                let resume = self.context.function.add_block();
                self.terminate(Terminator::r#yield(node.span, place, resume));
                self.context.point = InsertionPoint::End(resume);
            }

            K::Array(ids) => self.lower_array_into(node, ids, destination),

            // These operations exist only before final HIR elaboration. Their `Never` payloads make
            // that invariant part of the phase type while keeping this match exhaustive, so adding
            // a future HIR node forces MIR lowering to handle it at compile time.
            K::FieldAccess(never)
            | K::TraitMethodApply(never)
            | K::GetTraitMethod(never)
            | K::GetTraitAssociatedConst(never)
            | K::GetTraitDictionary(never) => match *never {},
        }
    }

    /// Interns a typed HIR immediate representation in the current function's constant pool.
    fn immediate_constant(&mut self, ty: Type, representation: LiteralValue) -> mir::Value {
        mir::Value::Constant(
            self.context
                .function
                .add_constant(ty, representation, &self.env),
        )
    }

    /// Inserts an operation, turning a source-fallible one into the current block's `Invoke`
    /// terminator and continuing in its explicit normal successor.
    fn insert(&mut self, operation: Operation) -> Option<mir::Value> {
        match operation.source_fallibility() {
            SourceFallibility::Fallible => return self.invoke(operation),
            SourceFallibility::Infallible => {}
            SourceFallibility::FromOpenProjection => {
                panic!("end_project must be emitted with its accessor call type")
            }
        }
        self.insert_infallible(operation)
    }

    /// Inserts an operation whose context-dependent source fallibility has already been resolved.
    fn insert_infallible(&mut self, operation: Operation) -> Option<mir::Value> {
        let InsertionPoint::End(block) = self.context.point;
        self.context.function.append_operation(block, operation)
    }

    /// Emits a source-fallible operation with explicit normal and source-error successors.
    fn invoke(&mut self, operation: Operation) -> Option<mir::Value> {
        let span = operation.span;
        let normal = self.context.function.add_block();
        let error = match self.context.cleanup_unwind_target {
            CleanupUnwindTarget::CurrentScope => self
                .innermost_pad(span)
                .unwrap_or_else(|| self.propagate_error_block(span)),
            CleanupUnwindTarget::Pad(target) => target,
            CleanupUnwindTarget::PropagateWithoutPad => self.propagate_error_block(span),
            CleanupUnwindTarget::FailureDuringCleanup => self.failure_during_cleanup_block(span),
        };
        let InsertionPoint::End(block) = self.context.point;
        let result = self
            .context
            .function
            .set_terminator(block, Terminator::invoke(span, operation, normal, error));
        self.context.point = InsertionPoint::End(normal);
        result
    }

    /// Terminates the current block.
    fn terminate(&mut self, terminator: Terminator) {
        let InsertionPoint::End(block) = self.context.point;
        self.context.function.set_terminator(block, terminator);
    }

    fn propagate_error_block(&mut self, span: Location) -> BlockId {
        if let Some(block) = self.context.propagate_error_block {
            return block;
        }
        let block = self.context.function.add_block();
        self.context
            .function
            .set_terminator(block, Terminator::propagate_error(span));
        self.context.propagate_error_block = Some(block);
        block
    }

    fn failure_during_cleanup_block(&mut self, span: Location) -> BlockId {
        if let Some(block) = self.context.failure_during_cleanup_block {
            return block;
        }
        let block = self.context.function.add_block();
        self.context
            .function
            .set_terminator(block, Terminator::failure_during_cleanup(span));
        self.context.failure_during_cleanup_block = Some(block);
        block
    }

    /// Returns whether the current insertion block already ends in a terminator (e.g. a `ret`
    /// emitted by an explicit `return`), so callers can avoid inserting after a terminator.
    fn current_block_is_terminated(&self) -> bool {
        match &self.context.point {
            InsertionPoint::End(b) => self.context.function.block_is_terminated(*b),
        }
    }

    /// Returns a textual representation of `x`.
    fn show<T: FormatWith<ModuleEnv<'a>>>(&self, x: T) -> String {
        format!("{}", x.format_with(&self.env))
    }
}

/// Construction state used while operations and terminators are emitted.
struct InsertionContext {
    /// The function being built.
    function: FunctionBuilder,

    /// The function we are lowering from.
    source: LocalFunctionId,

    /// The current pending block.
    point: InsertionPoint,

    /// The default source region for generated MIR.
    span: Location,

    /// The MIR places (pointer values) backing the function's locals, including explicit arguments
    /// (each passed by pointer) and any variables declared within the function.
    locals: FxHashMap<LocalDeclId, mir::Value>,

    /// The MIR values bound to extra parameters of the function.
    extra_parameters: FxHashMap<ExtraParameterId, mir::Value>,

    /// The `Value` dictionary parameters witnessing the run-time layout of generic types, used to
    /// allocate storage whose size is known only at run time.
    value_witnesses: Vec<(Type, mir::Value)>,

    /// The lexically enclosing loops, keyed by `LoopId`, used to lower `break`/`continue`.
    loops: FxHashMap<LoopId, LoopFrame>,

    /// The return out-pointer (the last parameter) into which the function writes its result.
    return_destination: mir::Value,

    /// Whether the lowered function itself returns a place (`SubscriptResultConvention::AddressorPlace`).
    /// When set, `return <expr>` lowers `<expr>` as a place and stores that pointer into the
    /// `**T` return out-pointer (mirrors the interpreter's `EvalCtx::returns_place`).
    returns_place: bool,

    /// The stack of active lexical scopes, innermost last. Each scope records the drop obligations
    /// of the locals it owns; the obligations are emitted as inline (init-guarded) `drop`
    /// operations at every control-transfer edge that unwinds the scope: a normal block exit
    /// drops its own scope, and a `return` drops all enclosing scopes.
    scopes: Vec<Scope>,

    /// Cleanup blocks whose bodies are deferred until function finalization. Each block captures its
    /// obligations and enclosing target when first referenced, then is filled through the builder
    /// after ordinary body lowering (see `fill_pending_pads`).
    pending_pads: Vec<PendingPad>,

    /// The error successor for a source-fallible operation emitted in the current context.
    cleanup_unwind_target: CleanupUnwindTarget,

    /// Shared terminal source-error exit, allocated lazily.
    propagate_error_block: Option<BlockId>,

    /// Shared terminal double-failure exit, allocated lazily.
    failure_during_cleanup_block: Option<BlockId>,
}

/// How lowering selects an explicit source-error successor.
#[derive(Clone, Copy)]
enum CleanupUnwindTarget {
    /// Normal function-body emission: derive a pad from the active lexical scopes.
    CurrentScope,
    /// Inline cleanup: if this action raises as the primary error, enter a pad for its pending
    /// siblings and/or enclosing scopes.
    Pad(BlockId),
    /// Do not attach another cleanup edge. This is used for outermost inline cleanup, whose primary
    /// error propagates to the caller, and inside landing pads, where a secondary error causes hard
    /// abort instead of a replacement unwind.
    PropagateWithoutPad,
    /// A source failure raised while another failure is already unwinding poisons execution.
    FailureDuringCleanup,
}

/// A cleanup landing pad awaiting its body (see `InsertionContext::pending_pads`).
struct PendingPad {
    /// The (allocated, initially empty) pad block.
    block: BlockId,

    /// This scope's cleanup actions to run in the pad, already reversed (innermost-declared last runs
    /// first), captured when the pad was allocated and the scope was still live.
    actions: Vec<CleanupAction>,

    /// The pad of the nearest enclosing scope with obligations, branched to after this pad's actions;
    /// `None` for the outermost pad, which terminates with `propagate_error`.
    outer: Option<BlockId>,

    /// The span the pad's actions are attributed to (the first exceptional edge that needed it).
    span: Location,
}

/// A lexical scope's deferred cleanup actions (in declaration order).
struct Scope {
    /// The cleanup to run when the scope exits — owned-local drops, and, for the dedicated scope a
    /// `WithYielded` opens, the `end_project` that runs the accessor slide. Run in reverse order on
    /// every exit (normal, transfer, and the error pad), so the slide runs after the body's own
    /// drops, on every path — matching the HIR interpreter's epilogue-on-exit.
    actions: Vec<CleanupAction>,

    /// The cleanup landing pad for this scope, built lazily the first time an exceptional edge nested
    /// in it needs an unwind target (see `allocate_pad`). The pad runs this scope's actions (reverse
    /// declaration order, init-guarded) and then chains to the nearest enclosing scope's pad or, if
    /// none, terminates with `propagate_error`. `None` until built (a scope
    /// with no obligations, or one no exceptional edge unwinds through, never gets one).
    pad: Option<BlockId>,
}

impl Scope {
    /// Adds an obligation and invalidates any pad that captured the previous action set.
    fn push_action(&mut self, action: CleanupAction) {
        self.actions.push(action);
        // `allocate_pad` snapshots the current actions. A later exceptional edge must allocate a
        // fresh pad containing this new obligation rather than reuse that stale snapshot.
        self.pad = None;
    }
}

/// A single deferred cleanup action run on scope exit, transfer, and the error pad.
#[derive(Clone)]
enum CleanupAction {
    /// Drop an owned local (init-guarded `Value::drop`).
    Drop(DropObligation),

    /// Close a scoped subscript: run the accessor slide and reclaim its frame (`end_project` of the
    /// place a `project` exposed). The projection binding is non-owning, so there is no drop.
    EndProject {
        place: mir::Value,
        call_ty: CallImplType,
    },
}

impl CleanupAction {
    /// Whether this action may start a source failure. Sandbox violations are executor exits and do
    /// not participate in the MIR source-error CFG.
    fn is_source_fallible(&self) -> bool {
        match self {
            Self::Drop(_) => false,
            Self::EndProject { call_ty, .. } => call_type_is_fallible(call_ty),
        }
    }
}

/// The lowering targets of an enclosing loop, used to resolve `break`/`continue` to it.
#[derive(Clone)]
struct LoopFrame {
    /// The loop's head block, branched to by `continue` and by the body's back-edge.
    head: BlockId,

    /// The loop's exit block, branched to by `break`; lowering continues here after the loop.
    exit: BlockId,

    /// The place into which `break` writes the loop's result (the loop's destination, or a
    /// throwaway temporary when the result is discarded).
    result: mir::Value,

    /// The stack marker captured before the loop; every iteration is reset to it, and `break`/
    /// `continue` reset to it before transferring, so per-iteration temporaries do not leak.
    marker: mir::Value,

    /// The scope-stack depth at loop entry. A `break`/`continue` unwinds the scopes above this
    /// depth (the ones entered inside the loop body) before transferring.
    scope_depth: usize,
}

/// A single deferred drop: the place to drop, the type of its pointee (to resolve a dictionary
/// `Value::drop` method), and how to dispatch the drop.
#[derive(Clone)]
struct DropObligation {
    place: mir::Value,
    dropped_ty: Type,
    spec: DropSpec,
}

/// Whether a call's source effect row can return a language failure, and so needs an explicit unwind
/// edge to a cleanup pad. A concrete `Fallible` primitive effect is exact; an unresolved effect
/// variable is treated conservatively as potentially fallible, so a generic callee that instantiates
/// fallibly still runs its caller's cleanup on the error path. Sandbox violations bypass this
/// source-error classification.
fn call_type_is_fallible(ty: &CallImplType) -> bool {
    ty.effects()
        .contains(crate::types::effects::Effect::Primitive(
            crate::types::effects::PrimitiveEffect::Fallible,
        ))
        || ty.effects().has_variables()
}

/// How a `Value::drop` is dispatched for a drop obligation.
#[derive(Clone, Copy)]
enum DropSpec {
    /// A concrete `Value::drop` implementation.
    Static(FunctionId),
    /// `Value::drop` loaded at run time from this hidden dictionary extra parameter.
    Dictionary(ExtraParameterId),
}

/// Where an operation should be inserted in a basic block.
#[derive(Clone, Copy)]
enum InsertionPoint {
    /// The end of a basic block.
    End(BlockId),
}
