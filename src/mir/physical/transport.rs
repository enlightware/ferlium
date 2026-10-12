// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! How a call's arguments reach the entry it calls.
//!
//! The ABI (`doc/abi.md`) passes a concrete scalar `Let` parameter of a direct entry by value, and
//! every other parameter through a pointer. Semantic MIR passes a scalar `Let` argument as a value
//! whenever its call-site type is concrete, whatever the callee. Physical MIR states the transport:
//! it keeps a value only where the entry takes the parameter directly, so physical lowering spills
//! the others into a place.
//!
//! The entry follows from the callee operand. A static function takes a parameter directly if its
//! own type, before instantiation, is a concrete scalar: a generic parameter is indirect even where
//! the call instantiates it to `int`. A dictionary entry is the trait method's declared type, also
//! per parameter. Every other dynamic callee, such as a stored callable, has a uniform entry that
//! takes everything indirectly.

use std::cell::OnceCell;

use rustc_hash::FxHashMap;

use crate::{
    compiler::MirArtifacts,
    hir::function::ArgConvention,
    mir::{Function, Operation, OperationKind, ParameterKind, Value, ValueId, operation},
    module::{CallableOrigin, FunctionId, ModuleEnv, TraitId, id::Id},
    types::r#trait::TraitDictionaryEntryIndex,
};

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
            Value::Function(callee) => self.function_takes_value(*callee, offset),
            Value::Register(id) => self.entries().get(id).is_some_and(|&(trait_id, entry)| {
                self.env
                    .trait_def(trait_id)
                    .methods
                    .get(entry.as_index())
                    .and_then(|(_, method)| method.ty_scheme.ty.args.get(offset))
                    .is_some_and(|argument| {
                        !argument
                            .mut_ty
                            .as_resolved()
                            .is_none_or(|mutability| mutability.is_mutable())
                            && operation::is_scalar_value_type(argument.ty)
                    })
            }),
            _ => false,
        }
    }

    fn function_takes_value(&self, callee: FunctionId, offset: usize) -> bool {
        if callee.module == self.env.current.module_id()
            && let Some(specialization) = self.semantic.specialization(callee.function)
        {
            return specialization
                .body
                .parameters()
                .iter()
                .filter(|parameter| {
                    matches!(
                        parameter.kind,
                        ParameterKind::Parameter(_) | ParameterKind::Owned
                    )
                })
                .nth(offset)
                .is_some_and(|parameter| {
                    parameter.kind == ParameterKind::Parameter(ArgConvention::Let)
                        && operation::is_scalar_value_type(parameter.ty)
                });
        }
        let Some(function) = self
            .env
            .module_by_id(callee.module)
            .and_then(|module| module.get_function_by_id(callee.function))
        else {
            return false;
        };
        let definition = &function.definition;
        // A native addressor borrows its root through a pointer, whatever the root's type.
        if matches!(function.origin, CallableOrigin::Native { .. })
            && definition.result_rooted_in == Some(offset as u32)
        {
            return false;
        }
        function.parameter_passing.get(offset) == Some(&ArgConvention::Let)
            && definition
                .ty_scheme
                .ty
                .args
                .get(offset)
                .is_some_and(|argument| operation::is_scalar_value_type(argument.ty))
    }
}
