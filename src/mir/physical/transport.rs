// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! How a call's arguments and result reach the entry it calls.
//!
//! The ABI (`doc/abi.md`) passes a concrete scalar `Let` parameter of a direct entry by value, and
//! every other parameter through a pointer; it returns a non-fallible concrete scalar result of a
//! direct entry by value, and every other result through a pointer. Semantic MIR passes a scalar
//! `Let` argument, and defines a scalar result register, whenever its call-site type says so,
//! whatever the callee. Physical MIR states the transport: it keeps a value only where the entry
//! takes the parameter or returns the result directly, so physical lowering passes a place for the
//! others. A call type more conservative than its callee, such as a devirtualized trait method
//! declared fallible, keeps a result place in semantic MIR, which physical lowering turns into a
//! value where the entry returns one.
//!
//! The entry follows from the callee operand. A native function's entry is its native signature.
//! A script function takes a parameter directly if its own type, before instantiation, is a
//! concrete scalar: a generic parameter is indirect even where the call instantiates it to `int`.
//! It returns its result directly under the same condition on its result and effects. A dictionary
//! entry is the trait method's declared type for its parameters, and returns through a pointer.
//! Every other dynamic callee, such as a stored callable, has a uniform entry that takes and
//! returns everything indirectly. The Wasm emitter derives the same entries.

use std::cell::OnceCell;

use rustc_hash::FxHashMap;

use crate::{
    compiler::MirArtifacts,
    hir::{
        function::ArgConvention,
        native_functions::{NativeParameter, NativeResult},
    },
    mir::{
        Function, Operation, OperationKind, Parameter, ResultTransport, Value, ValueId,
        edit::FunctionEdit,
        operation,
        results::definition_result_transport,
        terminator::{Terminator, TerminatorKind},
    },
    module::{CallableOrigin, FunctionId, ModuleEnv, TraitId, id::Id},
    types::{
        r#trait::TraitDictionaryEntryIndex,
        r#type::{CallResultConvention, Type},
    },
    ustr,
};

/// A devirtualized callback can have a wider source result than its native entry.
/// Call a diverging entry with its actual contract and private bottom storage;
/// it cannot initialize the caller's widened result. Preserve the failure edge,
/// including its cleanup, and trap if the native violates its Never contract.
pub(super) fn lower_diverging_native_calls(body: Function, env: ModuleEnv<'_>) -> Function {
    let candidates = body
        .blocks()
        .filter_map(|block| {
            let terminator = body.block(block).terminator();
            let TerminatorKind::Invoke { operation, .. } = &terminator.kind else {
                return None;
            };
            let OperationKind::Call { ty, .. } = &operation.kind else {
                return None;
            };
            let Value::Function(target) = operation.operands.first()? else {
                return None;
            };
            let entry = env
                .module_by_id(target.module)?
                .get_function_by_id(target.function)?
                .code
                .native_entry()?;
            (entry.signature().result == NativeResult::Never && ty.fn_ty.ret != Type::never())
                .then(|| (block, terminator.clone()))
        })
        .collect::<Vec<_>>();
    if candidates.is_empty() {
        return body;
    }
    let mut edit = FunctionEdit::new(body);
    for (block, mut terminator) in candidates {
        let TerminatorKind::Invoke {
            operation, normal, ..
        } = &mut terminator.kind
        else {
            unreachable!();
        };
        let mut storage = Operation::alloca(operation.span, Type::never());
        let slot = edit.assign_new_result(&mut storage).unwrap();
        let entry = edit.entry();
        edit.block_mut(entry).operations.insert(0, storage);
        let result_index = operation.call_result_place_index();
        let mut operands = operation.operands.to_vec();
        if let Some(index) = result_index {
            operands[index] = slot;
        } else {
            operands.push(slot);
        }
        operation.operands = operands.into_boxed_slice();
        operation.assign_result_id(None);
        let OperationKind::Call {
            ty,
            result_transport,
            ..
        } = &mut operation.kind
        else {
            unreachable!();
        };
        ty.fn_ty.ret = Type::never();
        ty.result_convention = CallResultConvention::Value;
        *result_transport = ResultTransport::Place;
        *normal = edit.add_block(Terminator::invariant_failure(
            operation.span,
            ustr("never native returned success"),
        ));
        edit.block_mut(block).terminator = terminator;
    }
    edit.remove_unreachable_blocks();
    edit.finish_unverified()
}

/// The entries the calls of one body reach.
pub(crate) struct Transports<'a> {
    func: &'a Function,
    semantic: &'a MirArtifacts,
    env: ModuleEnv<'a>,
    /// The dictionary entry each callee register selects, collected for the first dynamic callee.
    entries: OnceCell<FxHashMap<ValueId, (TraitId, TraitDictionaryEntryIndex)>>,
}

impl<'a> Transports<'a> {
    pub(crate) fn of(func: &'a Function, semantic: &'a MirArtifacts, env: ModuleEnv<'a>) -> Self {
        Self {
            func,
            semantic,
            env,
            entries: OnceCell::new(),
        }
    }

    fn entries(&self) -> &FxHashMap<ValueId, (TraitId, TraitDictionaryEntryIndex)> {
        self.entries.get_or_init(|| {
            self.func
                .blocks()
                .flat_map(|block| self.func.block(block).operations())
                .filter_map(|operation| match operation.kind {
                    OperationKind::DictEntry {
                        trait_id,
                        entry_index,
                        ..
                    } => Some((operation.result_id()?, (trait_id, entry_index))),
                    _ => None,
                })
                .collect()
        })
    }

    /// Whether the entry `call` reaches takes its visible argument at `offset` as a value.
    pub(crate) fn takes_value(&self, call: &Operation, offset: usize) -> bool {
        match &call.operands[0] {
            Value::Function(callee) => {
                self.function_takes_value(*callee, call.call_captures(), offset)
            }
            Value::Register(id) => self.entries().get(id).is_some_and(|&(trait_id, entry)| {
                self.env
                    .trait_def(trait_id)
                    .methods
                    .get(entry.as_index())
                    .and_then(|(_, method)| method.ty_scheme.ty.args.get(offset))
                    .is_some_and(|argument| operation::is_value_argument(argument, &self.env))
            }),
            _ => false,
        }
    }

    /// How the selected entry transports its result. Dynamic entries use an output place.
    pub(crate) fn result(&self, call: &Operation) -> ResultTransport {
        let Value::Function(callee) = &call.operands[0] else {
            return ResultTransport::Place;
        };
        if callee.module == self.env.current.module_id()
            && let Some(specialization) = self.semantic.specialization(callee.function)
        {
            return specialization.body.result_transport();
        }
        let Some(module) = self.env.module_by_id(callee.module) else {
            return ResultTransport::Place;
        };
        let Some(function) = module.get_function_by_id(callee.function) else {
            // A physical helper is built with the transport its calls state.
            return match &call.kind {
                OperationKind::Call {
                    result_transport, ..
                } => *result_transport,
                _ => ResultTransport::Place,
            };
        };
        // A storage primitive is expanded in place, from its result place.
        if matches!(function.origin, CallableOrigin::BufferPrimitive(_)) {
            return ResultTransport::Place;
        }
        if function.code.as_script().is_some() {
            return definition_result_transport(
                &function.definition,
                ModuleEnv::new(module, self.env.modules),
            );
        }
        match function
            .code
            .native_entry()
            .map(|entry| entry.signature().result)
        {
            Some(NativeResult::Unit) => ResultTransport::NoValue,
            Some(NativeResult::Scalar(..)) => ResultTransport::Value,
            _ => ResultTransport::Place,
        }
    }

    /// Whether `callee` takes visible argument `offset` as a value, where a call to a lambda passes
    /// `captures` value captures before its visible arguments.
    fn function_takes_value(&self, callee: FunctionId, captures: usize, offset: usize) -> bool {
        if callee.module == self.env.current.module_id()
            && let Some(specialization) = self.semantic.specialization(callee.function)
        {
            // A specialization's body lists the lambda's captures among its visible parameters.
            return specialization
                .body
                .parameters()
                .iter()
                .filter(|parameter| parameter.kind.is_visible())
                .nth(captures + offset)
                .is_some_and(Parameter::is_value);
        }
        let Some(function) = self
            .env
            .module_by_id(callee.module)
            .and_then(|module| module.get_function_by_id(callee.function))
        else {
            return false;
        };
        // A native entry states its transports, such as an addressor borrowing its root through a
        // pointer whatever the root's type.
        if let Some(entry) = function.code.native_entry() {
            return matches!(
                entry.signature().parameters.get(offset),
                Some(NativeParameter::Scalar(..))
            );
        }
        let definition = &function.definition;
        function.parameter_passing.get(offset) == Some(&ArgConvention::Let)
            && definition
                .ty_scheme
                .ty
                .args
                .get(offset)
                .is_some_and(|argument| operation::is_scalar_value_type(argument.ty, &self.env))
    }
}
