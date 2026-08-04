// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Compile-time evaluation of Ferlium calls, on top of the MIR reference interpreter.
//!
//! This is the engine the partial-evaluation passes ask "what does this call return?". It answers
//! with a runtime [`Value`] or refuses with a [`NotFoldable`] reason; it never produces a
//! compilation error, because Ferlium has no explicit const context yet and folding is purely
//! opportunistic. See `doc/plans/partial-evaluation.md`.
//!
//! Nothing here rewrites MIR: turning a returned value back into a constant is reification, which
//! is a separate concern.
//!
//! The engine has no caller yet — the folding pass that consumes it is a later phase — so its
//! items are exercised only by the tests below.
#![allow(dead_code)]

use crate::{
    CompilerSession, Location,
    compiler::MirOptimization,
    eval::RuntimeError,
    execution::{ExecutionLimits, ReferenceInterpreterLimits},
    hir::value::Value,
    mir::interpreter::{CallArgument, Interpreter},
    module::{FunctionId, ModuleId, TraitDictionaryId},
    types::{
        effects::{EffType, Effect, PrimitiveEffect},
        r#type::{CallResultConvention, Type},
    },
};

/// Fuel granted to a single compile-time evaluation.
///
/// These are a *compile-time budget*, not a runtime resource policy: they bound how much work the
/// compiler will do speculatively for one call, and exhausting them costs an optimization rather
/// than failing a program. They are deliberately generous and stable — a user who annotates a hot
/// path to make it foldable should not lose the optimization because an unrelated edit pushed a
/// computation across a threshold.
pub(crate) const CONST_EVAL_FUEL: usize = 100_000;

/// Call depth granted to a single compile-time evaluation.
pub(crate) const CONST_EVAL_CALL_DEPTH: usize = 64;

/// Interpreter environment cells granted to a single compile-time evaluation.
pub(crate) const CONST_EVAL_ENVIRONMENT_CELLS: usize = 16_384;

fn const_eval_limits() -> ReferenceInterpreterLimits {
    ReferenceInterpreterLimits::new(
        ExecutionLimits::new(CONST_EVAL_CALL_DEPTH, Some(CONST_EVAL_FUEL)),
        CONST_EVAL_ENVIRONMENT_CELLS,
    )
}

/// Why a call was not evaluated at compile time.
///
/// Every one of these is a normal outcome: the call stays in the program and runs at run time.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum NotFoldable {
    /// The call's declared effects do not permit compile-time execution.
    Effectful,
    /// The callee has no body the compiler can run.
    NoBody,
    /// The callee's result convention is not supported by compile-time evaluation.
    UnsupportedConvention,
    /// The call raised a source failure. It may equally fail at run time; folding it away would
    /// discard a failure the program is entitled to observe.
    Failed,
    /// The attempt exhausted its compile-time budget, or poisoned its evaluation context.
    BudgetExceeded,
    /// The call was evaluated, but its result cannot be expressed as MIR. Raised by
    /// [`reify`](crate::mir::reify::reify) rather than by the evaluator: today the constant pool
    /// holds only trivially-copyable representations, so a folded `String`, list, variant, or
    /// closure has nowhere to go. See Phase 5 of `doc/plans/partial-evaluation.md`.
    ///
    /// Worth reporting separately from the engine-level refusals: how often it occurs is what
    /// decides whether that phase is worth doing.
    NotReifiable,
}

/// Whether a call with these effects may be executed at compile time.
///
/// Effects are *trusted*, not verified: a native declaring neither `Read` nor `Write` is asserted
/// by its host to be pure and deterministic (see `doc/runtime-sandboxing.md`). `Fallible` is
/// permitted — a failing evaluation is simply not folded.
///
/// Effect *variables* are rejected. An unresolved variable means the instantiated effects are
/// unknown, which is exactly how `call_type_is_fallible` in the verifier treats them.
pub(crate) fn effects_allow_const_eval(effects: &EffType) -> bool {
    !effects.has_variables()
        && !effects.contains(Effect::Primitive(PrimitiveEffect::Read))
        && !effects.contains(Effect::Primitive(PrimitiveEffect::Write))
}

/// Whether a result convention can be evaluated at compile time.
///
/// Only [`CallResultConvention::Value`] produces a self-contained result. The subscript
/// conventions do not: an addressor yields a pointer into caller-rooted storage and a
/// `YieldedOnce` accessor suspends mid-way, so neither has a value to hand back once the
/// evaluation context is torn down.
pub(crate) fn convention_allows_const_eval(convention: CallResultConvention) -> bool {
    matches!(convention, CallResultConvention::Value)
}

/// Evaluates calls at compile time, in isolation from the session's runtime execution.
///
/// Each attempt runs in a fresh [`Interpreter`], so its environment and its poisoning state are
/// discarded with it: a compile-time evaluation that exceeds its budget can never poison an
/// execution domain the program later uses.
pub(crate) struct ConstEvaluator<'a> {
    session: &'a CompilerSession,
    /// Module context for the evaluation contexts this evaluator creates.
    module_id: ModuleId,
}

/// An argument to a compile-time call, in the callee's parameter order.
pub(crate) enum ConstArgument {
    /// A known value for a visible parameter.
    Value(Value),
    /// A symbolic trait dictionary for a hidden evidence parameter.
    Dictionary(TraitDictionaryId),
}

impl<'a> ConstEvaluator<'a> {
    pub(crate) fn new(module_id: ModuleId, session: &'a CompilerSession) -> Self {
        Self { session, module_id }
    }

    /// Evaluates `callee` applied to `arguments`, or explains why it cannot be.
    ///
    /// `effects` are the *call-site* effects — the instantiated ones from the call's
    /// `CallImplType`, not the callee's declared scheme — and `convention` its result convention.
    /// `result_ty` is the instantiated result type, used to shape the return storage.
    ///
    /// The returned value owns its storage: the evaluation context it was produced in is gone by
    /// the time this returns. Ownership of `arguments` is taken in every case, including refusal.
    pub(crate) fn try_call(
        &self,
        callee: FunctionId,
        effects: &EffType,
        convention: CallResultConvention,
        result_ty: Type,
        arguments: Vec<ConstArgument>,
        span: Location,
    ) -> Result<Value, NotFoldable> {
        if !effects_allow_const_eval(effects) {
            discard(arguments);
            return Err(NotFoldable::Effectful);
        }
        if !convention_allows_const_eval(convention) {
            discard(arguments);
            return Err(NotFoldable::UnsupportedConvention);
        }
        if !self.callee_has_body(callee) {
            discard(arguments);
            return Err(NotFoldable::NoBody);
        }

        // A fresh interpreter per attempt is what makes compile-time evaluation isolated: its
        // environment and its poisoning state die with it. Bodies come from the raw stage, since
        // the optimized stage of the module being optimized is still being built.
        let mut interpreter = Interpreter::with_limits_and_stage(
            self.module_id,
            self.session,
            const_eval_limits(),
            MirOptimization::Disabled,
        );
        let arguments = arguments
            .into_iter()
            .map(|argument| match argument {
                ConstArgument::Value(value) => CallArgument::Value(value),
                ConstArgument::Dictionary(id) => CallArgument::Dictionary(id),
            })
            .collect();
        interpreter
            .call_with_known_arguments(callee, arguments, result_ty, span)
            .map_err(classify)
    }

    /// Whether the compiler can run this callee at all: a script function needs a lowered body, a
    /// native needs none.
    fn callee_has_body(&self, callee: FunctionId) -> bool {
        let module = self.session.expect_fresh_module(callee.module);
        let Some(function) = module.get_function_by_id(callee.function) else {
            return false;
        };
        if function.code.as_ref().as_script().is_none() {
            // A native's implementation is its Rust code, always available.
            return true;
        }
        self.session
            .mir_artifacts_for(callee.module, MirOptimization::Disabled)
            .and_then(|artifacts| artifacts.get(callee.function))
            .is_some()
    }
}

fn discard(arguments: Vec<ConstArgument>) {
    for argument in arguments {
        if let ConstArgument::Value(value) = argument {
            value.discard_storage();
        }
    }
}

/// Maps a runtime outcome to a refusal reason. Nothing escapes as a compilation error.
fn classify(error: RuntimeError) -> NotFoldable {
    match error {
        RuntimeError::SourceFailure(_) => NotFoldable::Failed,
        RuntimeError::SandboxViolation(_) | RuntimeError::FailureDuringCleanup(_) => {
            NotFoldable::BudgetExceeded
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ExecutionTarget,
        mir::{Function, OperationKind, terminator::TerminatorKind},
        module::{LocalFunctionId, Path, id::Id},
        types::effects::effect,
        types::r#type::CallImplType,
    };

    /// A call site extracted from real lowered MIR, with everything compile-time evaluation needs.
    struct CallSite {
        callee: FunctionId,
        ty: CallImplType,
    }

    /// Compiles `src` and returns its module id.
    fn compile(session: &mut CompilerSession, src: &str) -> ModuleId {
        session
            .compile_for(ExecutionTarget::Mir, src, "test", Path::single_str("test"))
            .expect("test source must compile")
            .module_id
    }

    fn body<'a>(session: &'a CompilerSession, module: ModuleId, name: &str) -> &'a Function {
        let id = session
            .expect_fresh_module(module)
            .get_local_function_id(crate::ustr(name))
            .unwrap_or_else(|| panic!("no function named {name}"));
        session
            .mir_artifacts_for(module, MirOptimization::Disabled)
            .expect("MIR must be prepared")
            .get(id)
            .expect("function must have a MIR body")
    }

    fn function_id(session: &CompilerSession, module: ModuleId, name: &str) -> FunctionId {
        FunctionId {
            module,
            function: session
                .expect_fresh_module(module)
                .get_local_function_id(crate::ustr(name))
                .unwrap_or_else(|| panic!("no function named {name}")),
        }
    }

    /// Collects every statically-resolved call in `func`, in traversal order.
    ///
    /// Driving the tests off real lowering rather than hand-built inputs is deliberate: it checks
    /// that the metadata a `Call` already carries is enough to run it, which is exactly what the
    /// folding pass will rely on.
    fn call_sites(func: &Function) -> Vec<CallSite> {
        let mut sites = Vec::new();
        let mut collect = |operation: &crate::mir::Operation| {
            if let OperationKind::Call { ty } = &operation.kind
                && let crate::mir::Value::Function(callee) = &operation.operands[0]
            {
                sites.push(CallSite {
                    callee: *callee,
                    ty: ty.as_ref().clone(),
                });
            }
        };
        for block_id in func.blocks() {
            let block = func.block(block_id);
            for operation in block.operations() {
                collect(operation);
            }
            if let TerminatorKind::Invoke { operation, .. } = &block.terminator().kind {
                collect(operation);
            }
        }
        sites
    }

    fn try_call(
        session: &CompilerSession,
        module: ModuleId,
        site: &CallSite,
        arguments: Vec<ConstArgument>,
    ) -> Result<Value, NotFoldable> {
        ConstEvaluator::new(module, session).try_call(
            site.callee,
            site.ty.effects(),
            site.ty.result_convention,
            site.ty.ret(),
            arguments,
            Location::new_synthesized(),
        )
    }

    /// Reduces an outcome to its refusal reason, releasing any value produced. `Value` is not
    /// comparable, and a folded result owns storage that must not leak in a test either.
    fn refusal(result: Result<Value, NotFoldable>) -> Option<NotFoldable> {
        match result {
            Ok(value) => {
                value.discard_storage();
                None
            }
            Err(reason) => Some(reason),
        }
    }

    fn int(value: isize) -> ConstArgument {
        ConstArgument::Value(Value::native(value))
    }

    /// The path that matters most: the natives every arithmetic operator lowers to.
    #[test]
    fn evaluates_a_native_arithmetic_impl() {
        let mut session = CompilerSession::new();
        let module = compile(&mut session, "fn f() -> int { 2 + 3 }");
        // The last statically-resolved call of `f` is the addition; the earlier ones convert the
        // literals through `Num::from_int`.
        let sites = call_sites(body(&session, module, "f"));
        let add = sites.last().expect("`2 + 3` lowers to a call");

        let result = try_call(&session, module, add, vec![int(2), int(3)])
            .expect("adding two known integers must fold");
        assert_eq!(result.as_primitive_ty::<isize>(), Some(&5));
        result.discard_storage();
    }

    /// A native returning heap data, to check the result survives its evaluation context.
    #[test]
    fn evaluates_a_native_returning_heap_data() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn f() -> string { string_concat(\"ab\", \"cd\") }",
        );
        let sites = call_sites(body(&session, module, "f"));
        let concat = sites
            .iter()
            .find(|site| {
                session
                    .expect_fresh_module(site.callee.module)
                    .get_function_name_by_id(site.callee.function)
                    .is_some_and(|name| name == "string_concat")
            })
            .expect("`string_concat` must be called directly");

        let arguments = vec![
            ConstArgument::Value(Value::native(crate::std::string::String::from(
                "ab".to_string(),
            ))),
            ConstArgument::Value(Value::native(crate::std::string::String::from(
                "cd".to_string(),
            ))),
        ];
        let result = try_call(&session, module, concat, arguments)
            .expect("concatenating two known strings must fold");
        assert_eq!(
            result
                .as_primitive_ty::<crate::std::string::String>()
                .map(AsRef::as_ref),
            Some("abcd")
        );
        result.discard_storage();
    }

    #[test]
    fn evaluates_a_script_function() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn double(x: int) -> int { x + x }\nfn f() -> int { double(21) }",
        );
        let sites = call_sites(body(&session, module, "f"));
        let call = sites
            .iter()
            .find(|site| site.callee == function_id(&session, module, "double"))
            .expect("`double` must be called directly");

        let result =
            try_call(&session, module, call, vec![int(21)]).expect("a pure script call must fold");
        assert_eq!(result.as_primitive_ty::<isize>(), Some(&42));
        result.discard_storage();
    }

    /// A call that raises must not be folded: the program is entitled to observe that failure.
    #[test]
    fn refuses_a_call_that_fails() {
        let mut session = CompilerSession::new();
        // Integer division is `Fallible`: it is const-evaluable in principle, and refused here
        // only because this particular evaluation raises.
        let module = compile(&mut session, "fn f() -> int { idiv(1, 0) }");
        let sites = call_sites(body(&session, module, "f"));
        let div = sites
            .iter()
            .find(|site| {
                session
                    .expect_fresh_module(site.callee.module)
                    .get_function_name_by_id(site.callee.function)
                    .is_some_and(|name| name == "idiv")
            })
            .expect("`idiv` must be called directly");

        assert_eq!(
            refusal(try_call(&session, module, div, vec![int(1), int(0)])),
            Some(NotFoldable::Failed)
        );
    }

    /// Exhausting the compile-time budget costs an optimization, never a program.
    #[test]
    fn refuses_a_call_that_exhausts_its_budget() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn spin(n: int) -> int { if n <= 0 { 0 } else { spin(n - 1) } }\n\
             fn f() -> int { spin(1) }",
        );
        let sites = call_sites(body(&session, module, "f"));
        let call = sites
            .iter()
            .find(|site| site.callee == function_id(&session, module, "spin"))
            .expect("`spin` must be called directly");

        // Far beyond the compile-time call-depth budget.
        let deep = CONST_EVAL_CALL_DEPTH as isize * 100;
        assert_eq!(
            refusal(try_call(&session, module, call, vec![int(deep)])),
            Some(NotFoldable::BudgetExceeded)
        );

        // The session is untouched: a poisoned compile-time evaluation is discarded with its
        // interpreter, so ordinary execution still works.
        let f = function_id(&session, module, "f");
        assert!(
            session
                .run_entry(ExecutionTarget::Mir, module, f.function, vec![])
                .is_ok(),
            "a refused compile-time evaluation must not poison the session"
        );
    }

    /// A refused call must release every argument, including the ones it never bound.
    ///
    /// `Value` is `ManuallyDrop`-based, so an argument that is dropped rather than discarded leaks
    /// its Rust payload — a Ferlium `String`'s heap buffer, for instance. The interpreter reclaims
    /// what reached a cell when it truncates the frame; this covers the arguments that did not,
    /// because binding ran out of environment cells partway through.
    #[test]
    fn arguments_are_released_when_binding_runs_out_of_cells() {
        use std::sync::atomic::{AtomicUsize, Ordering};

        static DROPPED: AtomicUsize = AtomicUsize::new(0);

        #[derive(Debug)]
        struct DropTracked;

        impl Drop for DropTracked {
            fn drop(&mut self) {
                DROPPED.fetch_add(1, Ordering::Relaxed);
            }
        }

        impl crate::hir::value::NativeDisplay for DropTracked {
            fn fmt_repr(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "<drop-tracked>")
            }
        }

        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn add3(a: int, b: int, c: int) -> int { a + b + c }",
        );
        let callee = function_id(&session, module, "add3");

        // One cell: the first argument binds, the second is refused by `alloc_cell`, and the third
        // is never even reached — the case that leaks if a refusal only reclaims bound cells. The
        // callee is never entered, so the tracked natives stand in for values of any type without
        // being read.
        let limits = ReferenceInterpreterLimits::new(ExecutionLimits::new(8, Some(1_000)), 1);
        let mut interpreter = Interpreter::with_limits_and_stage(
            module,
            &session,
            limits,
            MirOptimization::Disabled,
        );
        let arguments = vec![
            CallArgument::Value(Value::native(DropTracked)),
            CallArgument::Value(Value::native(DropTracked)),
            CallArgument::Value(Value::native(DropTracked)),
        ];
        let result = interpreter.call_with_known_arguments(
            callee,
            arguments,
            crate::std::math::int_type(),
            Location::new_synthesized(),
        );
        assert!(result.is_err(), "binding must run out of cells");
        assert_eq!(
            DROPPED.load(Ordering::Relaxed),
            3,
            "an argument that was never bound must still be released"
        );
    }

    /// The two halves the folding pass needs, joined: evaluate a real call site, then express its
    /// result as MIR.
    #[test]
    fn a_folded_arithmetic_result_reifies_into_a_constant() {
        use crate::mir::reify::{Reification, reify};

        let mut session = CompilerSession::new();
        let module = compile(&mut session, "fn f() -> int { 2 + 3 }");
        let sites = call_sites(body(&session, module, "f"));
        let add = sites.last().expect("`2 + 3` lowers to a call");

        let result = try_call(&session, module, add, vec![int(2), int(3)]).expect("must fold");
        let env = session
            .modules()
            .env_for(session.expect_fresh_module(module));
        let reified = match reify(&result, add.ty.ret(), &env) {
            Ok(Reification::Constant(constant)) => constant,
            other => panic!("an integer result must reify into a constant, got {other:?}"),
        };
        assert_eq!(reified.representation.as_primitive_ty::<isize>(), Some(&5));
        result.discard_storage();
    }

    /// The same call site shape with a heap result: it evaluates, and reification is what refuses.
    /// Phase 5 of `doc/plans/partial-evaluation.md` is what would lift this.
    #[test]
    fn a_folded_string_result_is_not_reifiable() {
        use crate::mir::reify::is_reifiable;

        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn f() -> string { string_concat(\"ab\", \"cd\") }",
        );
        let sites = call_sites(body(&session, module, "f"));
        let concat = sites
            .iter()
            .find(|site| {
                session
                    .expect_fresh_module(site.callee.module)
                    .get_function_name_by_id(site.callee.function)
                    .is_some_and(|name| name == "string_concat")
            })
            .expect("`string_concat` must be called directly");

        let arguments = vec![
            ConstArgument::Value(Value::native(crate::std::string::String::from(
                "ab".to_string(),
            ))),
            ConstArgument::Value(Value::native(crate::std::string::String::from(
                "cd".to_string(),
            ))),
        ];
        let result = try_call(&session, module, concat, arguments).expect("must fold");
        let env = session
            .modules()
            .env_for(session.expect_fresh_module(module));
        assert!(!is_reifiable(&result, concat.ty.ret(), &env));
        result.discard_storage();
    }

    #[test]
    fn refuses_a_callee_without_a_body() {
        let mut session = CompilerSession::new();
        let module = compile(&mut session, "fn f() -> int { 2 + 3 }");
        let sites = call_sites(body(&session, module, "f"));
        let mut site = sites.last().expect("`2 + 3` lowers to a call").ty.clone();
        site.result_convention = CallResultConvention::Value;
        let missing = CallSite {
            // A local function id past the end of the module's dense function table.
            callee: FunctionId {
                module,
                function: LocalFunctionId::from_index(usize::from(u16::MAX)),
            },
            ty: site,
        };

        assert_eq!(
            refusal(try_call(&session, module, &missing, vec![int(2), int(3)])),
            Some(NotFoldable::NoBody)
        );
    }

    #[test]
    fn refuses_effectful_and_unsupported_conventions() {
        let mut session = CompilerSession::new();
        let module = compile(&mut session, "fn f() -> int { 2 + 3 }");
        let sites = call_sites(body(&session, module, "f"));
        let add = sites.last().expect("`2 + 3` lowers to a call");

        let mut effectful = add.ty.clone();
        effectful.fn_ty.effects = effect(PrimitiveEffect::Write);
        assert_eq!(
            refusal(try_call(
                &session,
                module,
                &CallSite {
                    callee: add.callee,
                    ty: effectful
                },
                vec![int(2), int(3)]
            )),
            Some(NotFoldable::Effectful)
        );

        let mut place_returning = add.ty.clone();
        place_returning.result_convention = CallResultConvention::ADDRESSOR_PLACE;
        assert_eq!(
            refusal(try_call(
                &session,
                module,
                &CallSite {
                    callee: add.callee,
                    ty: place_returning
                },
                vec![int(2), int(3)]
            )),
            Some(NotFoldable::UnsupportedConvention)
        );
    }

    #[test]
    fn effect_variables_are_rejected() {
        use crate::types::effects::EffectVar;

        assert!(effects_allow_const_eval(&EffType::empty()));
        assert!(effects_allow_const_eval(&effect(PrimitiveEffect::Fallible)));
        assert!(!effects_allow_const_eval(&effect(PrimitiveEffect::Read)));
        assert!(!effects_allow_const_eval(&effect(PrimitiveEffect::Write)));
        assert!(!effects_allow_const_eval(&EffType::single(
            Effect::Variable(EffectVar::new(0))
        )));
    }
}
