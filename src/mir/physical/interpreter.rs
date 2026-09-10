// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

//! Checked scalar physical-MIR execution. Boxed values exist only at the host boundary.
//! Unsupported reachable contracts are rejected before execution, even in untaken branches.

#[path = "interpreter_memory.rs"]
mod memory;

use super::program::ResolvedPhysicalProgram;
use crate::{
    Location,
    compiler::error::SandboxViolationKind,
    eval::RuntimeError,
    execution::ReferenceInterpreterLimits,
    hir::{
        function::ArgConvention,
        native_functions::{NativeEntry, NativeFailureState, NativeParameter, NativeResult},
        value::Value,
    },
    mir::{
        self, Function, Operation, OperationKind, function::ParameterKind,
        terminator::TerminatorKind,
    },
    module::{FunctionId, id::Id},
    types::r#type::CallResultConvention,
};
use memory::{Address, Memory, Scalar, ScalarKind};
use rustc_hash::{FxHashMap, FxHashSet};

fn unsupported(detail: impl std::fmt::Display) -> RuntimeError {
    RuntimeError::Backend(format!(
        "Physical MIR execution does not yet support {detail}"
    ))
}
fn invalid(detail: &str) -> RuntimeError {
    RuntimeError::Backend(format!("Invalid physical MIR execution: {detail}"))
}

#[derive(Clone, Copy)]
enum Binding {
    Scalar(Scalar),
    Place(Address),
    StackMarker(usize),
}

impl Binding {
    fn place(self) -> Result<Address, RuntimeError> {
        match self {
            Self::Place(address) => Ok(address),
            _ => Err(invalid("expected a place")),
        }
    }
    fn scalar(self) -> Result<Scalar, RuntimeError> {
        match self {
            Self::Scalar(value) => Ok(value),
            _ => Err(invalid("expected a scalar register")),
        }
    }
}

pub(crate) fn run_entry(
    program: &ResolvedPhysicalProgram,
    entry: FunctionId,
    arguments: &[Value],
    limits: ReferenceInterpreterLimits,
) -> Result<Value, RuntimeError> {
    let mut interpreter = Interpreter {
        program,
        memory: Memory::default(),
        limits,
        fuel: limits.execution.fuel_limit,
        depth: 0,
    };
    interpreter.check_supported(entry)?;
    let body = program
        .function(entry)
        .ok_or_else(|| unsupported("native host entry points"))?;
    let (result, parameters) = body
        .parameters()
        .split_last()
        .ok_or_else(|| invalid("missing result parameter"))?;
    if parameters.len() != arguments.len()
        || parameters.iter().any(|p| {
            !matches!(
                p.kind,
                ParameterKind::Parameter(ArgConvention::Let) | ParameterKind::Owned
            )
        })
    {
        return Err(unsupported("this host entry signature"));
    }
    let mut bindings = Vec::with_capacity(arguments.len() + 1);
    for (parameter, argument) in parameters.iter().zip(arguments) {
        let scalar = Scalar::from_value(argument)?;
        let kind = ScalarKind::for_type(parameter.ty)?;
        if scalar.kind() != kind {
            return Err(invalid("host argument type differs from parameter"));
        }
        let address = interpreter.allocate(kind, None)?;
        interpreter.memory.write(address, scalar)?;
        bindings.push(Binding::Place(address));
    }
    let result = interpreter.allocate(ScalarKind::for_type(result.ty)?, None)?;
    bindings.push(Binding::Place(result));
    interpreter.call(entry, bindings)?;
    // Supported values are trivially destructible. Memory reclaims all allocations on every exit.
    Ok(interpreter.memory.read(result)?.boxed())
}

struct Interpreter<'a, 'p> {
    program: &'a ResolvedPhysicalProgram<'p>,
    memory: Memory,
    limits: ReferenceInterpreterLimits,
    fuel: Option<usize>,
    depth: usize,
}

impl<'a, 'p> Interpreter<'a, 'p> {
    fn native(&self, id: FunctionId) -> Result<&'a NativeEntry, RuntimeError> {
        self.program
            .module(id.module)
            .and_then(|m| m.native_entry(id))
            .ok_or_else(|| unsupported(format!("native entry {id:?}")))
    }

    /// Capability checking of reachable callees, not another verifier or a whole-std scan.
    fn check_supported(&self, entry: FunctionId) -> Result<(), RuntimeError> {
        let mut pending = vec![entry];
        let mut visited = FxHashSet::default();
        while let Some(id) = pending.pop() {
            if !visited.insert(id) {
                continue;
            }
            let Some(body) = self.program.function(id) else {
                let native = self.native(id)?;
                if !native.supports_physical_call() {
                    return Err(unsupported("this native adapter"));
                }
                for parameter in &native.signature().parameters {
                    ScalarKind::for_native(parameter.layout())?;
                }
                match native.signature().result {
                    NativeResult::Scalar(layout, _) | NativeResult::Output(layout) => {
                        ScalarKind::for_native(layout)?;
                    }
                    NativeResult::Unit | NativeResult::Never => (),
                    _ => return Err(unsupported("optional or addressor native results")),
                }
                continue;
            };
            if body.result_convention() != CallResultConvention::Value {
                return Err(unsupported("place/yield call conventions"));
            }
            for parameter in body.parameters() {
                if parameter.kind == ParameterKind::Dictionary {
                    return Err(unsupported("generic evidence"));
                }
                ScalarKind::for_type(parameter.ty)?;
            }
            for constant in body.constants() {
                Scalar::from_literal(&constant.representation)?;
            }
            for block in body.blocks() {
                let block = body.block(block);
                for operation in block.operations() {
                    Self::check_operation(operation, &mut pending)?;
                }
                match &block.terminator().kind {
                    TerminatorKind::Invoke { operation, .. } => {
                        Self::check_operation(operation, &mut pending)?
                    }
                    TerminatorKind::Goto { .. }
                    | TerminatorKind::CondBr { .. }
                    | TerminatorKind::Return
                    | TerminatorKind::PropagateError
                    | TerminatorKind::FailureDuringCleanup
                    | TerminatorKind::InvariantFailure { .. } => (),
                    _ => return Err(unsupported("variant switches or yielded places")),
                }
            }
        }
        Ok(())
    }

    fn check_operation(
        operation: &Operation,
        pending: &mut Vec<FunctionId>,
    ) -> Result<(), RuntimeError> {
        use OperationKind::*;
        match &operation.kind {
            Alloca { ty } => {
                ScalarKind::for_type(*ty)?;
                if !operation.operands.is_empty() {
                    return Err(unsupported("dynamic layouts"));
                }
            }
            Clone { ty } | Drop { ty } => {
                ScalarKind::for_type(*ty)?;
                let index = if matches!(operation.kind, Clone { .. }) {
                    2
                } else {
                    1
                };
                match operation.operands[index] {
                    mir::Value::Function(id) if operation.operands.len() == index + 1 => {
                        pending.push(id)
                    }
                    _ => return Err(unsupported("indirect lifecycle calls or hidden evidence")),
                }
            }
            Call { .. } => match operation.operands[0] {
                mir::Value::Function(id) => pending.push(id),
                _ => return Err(unsupported("indirect calls")),
            },
            CompareEqual => {
                let mir::Value::Pattern(pattern) = &operation.operands[1] else {
                    return Err(invalid("expected literal pattern"));
                };
                Scalar::from_literal(pattern)?;
            }
            Load | Store | Clear | Memcpy | Move | Replace | IsInitialized | StackSave
            | StackRestore | CheckCallDepth | CheckFuel => (),
            _ => return Err(unsupported("aggregate, address, or callable operations")),
        }
        Ok(())
    }

    fn allocate(
        &mut self,
        kind: ScalarKind,
        span: Option<Location>,
    ) -> Result<Address, RuntimeError> {
        // Reuse the API's existing storage-slot guard; this is not a byte-memory quota.
        if self.memory.len() >= self.limits.environment_cell_limit {
            return Err(RuntimeError::new_sandbox_violation(
                SandboxViolationKind::EnvironmentCellLimitExceeded {
                    limit: self.limits.environment_cell_limit,
                },
                span,
            ));
        }
        self.memory.allocate(kind)
    }

    fn call(&mut self, id: FunctionId, args: Vec<Binding>) -> Result<(), RuntimeError> {
        let Some(body) = self.program.function(id) else {
            return self.call_native(id, &args);
        };
        if args.len() != body.parameters().len() {
            return Err(invalid("call arity mismatch"));
        }
        for (argument, parameter) in args.iter().zip(body.parameters()) {
            if argument.place()?.kind != ScalarKind::for_type(parameter.ty)? {
                return Err(invalid("call argument type mismatch"));
            }
        }
        // Explicit CheckCallDepth operations preserve the boxed executor's source-level policy.
        let marker = self.memory.len();
        self.depth += 1;
        let result = self.run_frame(body, &args, marker);
        self.depth -= 1;
        self.memory.restore(marker);
        result
    }

    fn operand(
        body: &Function,
        args: &[Binding],
        registers: &FxHashMap<mir::ValueId, Binding>,
        operand: &mir::Value,
    ) -> Result<Binding, RuntimeError> {
        match operand {
            mir::Value::Constant(id) => Ok(Binding::Scalar(Scalar::from_literal(
                &body.constant(*id).representation,
            )?)),
            mir::Value::Parameter(id) => args
                .get(id.as_index())
                .copied()
                .ok_or_else(|| invalid("unbound parameter")),
            mir::Value::Register(id) => registers
                .get(id)
                .copied()
                .ok_or_else(|| invalid("unbound register")),
            _ => Err(invalid("unsupported operand")),
        }
    }

    fn run_frame(
        &mut self,
        body: &Function,
        args: &[Binding],
        frame_base: usize,
    ) -> Result<(), RuntimeError> {
        let mut registers = FxHashMap::default();
        let mut block = body.entry();
        let mut pending: Option<RuntimeError> = None;
        let mut secondary: Option<RuntimeError> = None;
        loop {
            let current = body.block(block);
            for operation in current.operations() {
                self.operation(body, args, &mut registers, operation, frame_base)
                    .map_err(|error| match pending.take() {
                        Some(initial) => initial.interrupted_by(error),
                        None => error,
                    })?;
            }
            match &current.terminator().kind {
                TerminatorKind::Goto { target } => block = *target,
                TerminatorKind::CondBr {
                    condition,
                    then_target,
                    else_target,
                } => {
                    let Scalar::Bool(taken) =
                        Self::operand(body, args, &registers, condition)?.scalar()?
                    else {
                        return Err(invalid("non-boolean branch condition"));
                    };
                    block = if taken { *then_target } else { *else_target };
                }
                TerminatorKind::Invoke {
                    operation,
                    normal,
                    error,
                } => match self.operation(body, args, &mut registers, operation, frame_base) {
                    Ok(()) => block = *normal,
                    Err(failure @ RuntimeError::SourceFailure(_)) => {
                        if pending.is_none() {
                            pending = Some(failure);
                        } else {
                            secondary = Some(failure);
                        }
                        block = *error;
                    }
                    Err(failure) => {
                        return Err(match pending.take() {
                            Some(initial) => initial.interrupted_by(failure),
                            None => failure,
                        });
                    }
                },
                TerminatorKind::Return => {
                    if pending.is_some() {
                        return Err(invalid("return during source failure"));
                    }
                    return Ok(());
                }
                TerminatorKind::PropagateError => {
                    return Err(pending.ok_or_else(|| invalid("no failure to propagate"))?);
                }
                TerminatorKind::FailureDuringCleanup => {
                    return Err(pending
                        .ok_or_else(|| invalid("no initial cleanup failure"))?
                        .interrupted_by(
                            secondary.ok_or_else(|| invalid("no secondary cleanup failure"))?,
                        ));
                }
                TerminatorKind::InvariantFailure { message } => {
                    eprintln!("Ferlium invariant failure: {message}");
                    std::process::abort();
                }
                _ => unreachable!("capability check rejected this terminator"),
            }
        }
    }

    fn operation(
        &mut self,
        body: &Function,
        args: &[Binding],
        registers: &mut FxHashMap<mir::ValueId, Binding>,
        operation: &Operation,
        frame_base: usize,
    ) -> Result<(), RuntimeError> {
        use OperationKind::*;
        let operand =
            |index: usize| Self::operand(body, args, registers, &operation.operands[index]);
        let place = |index| operand(index)?.place();
        let result = match &operation.kind {
            Alloca { ty } => Some(Binding::Place(
                self.allocate(ScalarKind::for_type(*ty)?, Some(operation.span))?,
            )),
            Load => Some(Binding::Scalar(self.memory.read(place(0)?)?)),
            Store => {
                self.memory.write(place(1)?, operand(0)?.scalar()?)?;
                None
            }
            Clear => {
                self.memory.clear(place(0)?)?;
                None
            }
            IsInitialized => Some(Binding::Scalar(Scalar::Bool(
                self.memory.initialized(place(0)?)?,
            ))),
            Memcpy | Move => {
                let source = place(0)?;
                let destination = place(1)?;
                let value = self.memory.read(source)?;
                self.memory.write(destination, value)?;
                if matches!(operation.kind, Move) && source != destination {
                    self.memory.clear(source)?;
                }
                None
            }
            Replace => {
                let source = place(0)?;
                let destination = place(1)?;
                if source == destination || source.kind != destination.kind {
                    return Err(invalid("invalid replacement storage"));
                }
                let replacement = self.memory.read(source)?;
                let old = self
                    .memory
                    .initialized(destination)?
                    .then(|| self.memory.read(destination))
                    .transpose()?;
                self.memory.clear(source)?;
                self.memory.clear(destination)?;
                self.memory.write(destination, replacement)?;
                if let Some(old) = old {
                    self.memory.write(source, old)?;
                }
                None
            }
            Clone { .. } => {
                let mir::Value::Function(id) = operation.operands[2] else {
                    unreachable!()
                };
                self.call(id, vec![operand(0)?, operand(1)?])
                    .map_err(|error| error.with_frame(id, operation.span))?;
                None
            }
            Drop { .. } => {
                let address = place(0)?;
                if self.memory.initialized(address)? {
                    let mir::Value::Function(id) = operation.operands[1] else {
                        unreachable!()
                    };
                    let marker = self.memory.len();
                    let result = self.allocate(ScalarKind::Unit, Some(operation.span))?;
                    let outcome =
                        self.call(id, vec![Binding::Place(address), Binding::Place(result)]);
                    self.memory.restore(marker);
                    outcome.map_err(|error| error.with_frame(id, operation.span))?;
                    self.memory.clear(address)?;
                }
                None
            }
            CompareEqual => {
                let mir::Value::Pattern(pattern) = &operation.operands[1] else {
                    return Err(invalid("expected literal pattern"));
                };
                let value = match operand(0)? {
                    Binding::Place(address) => self.memory.read(address)?,
                    value => value.scalar()?,
                };
                Some(Binding::Scalar(Scalar::Bool(
                    value == Scalar::from_literal(pattern)?,
                )))
            }
            Call { .. } => {
                let mir::Value::Function(id) = operation.operands[0] else {
                    unreachable!()
                };
                let values = operation.operands[1..]
                    .iter()
                    .map(|value| Self::operand(body, args, registers, value))
                    .collect::<Result<Vec<_>, _>>()?;
                self.call(id, values)
                    .map_err(|error| error.with_frame(id, operation.span))?;
                None
            }
            StackSave => Some(Binding::StackMarker(self.memory.len())),
            StackRestore => {
                let Binding::StackMarker(marker) = operand(0)? else {
                    return Err(invalid("expected stack marker"));
                };
                if marker < frame_base || marker > self.memory.len() {
                    return Err(invalid("stack marker outside frame"));
                }
                self.memory.restore(marker);
                None
            }
            CheckCallDepth => {
                if self.depth >= self.limits.execution.call_depth_limit {
                    return Err(RuntimeError::new_sandbox_violation(
                        SandboxViolationKind::CallDepthLimitExceeded {
                            limit: self.limits.execution.call_depth_limit,
                        },
                        Some(operation.span),
                    ));
                }
                None
            }
            CheckFuel => {
                if let Some(fuel) = &mut self.fuel {
                    if *fuel == 0 {
                        return Err(RuntimeError::new_sandbox_violation(
                            SandboxViolationKind::FuelExhausted,
                            Some(operation.span),
                        ));
                    }
                    *fuel -= 1;
                }
                None
            }
            _ => unreachable!("capability check rejected this operation"),
        };
        if let Some(value) = result {
            registers.insert(
                operation.result_id().expect("value-producing operation"),
                value,
            );
        }
        Ok(())
    }

    fn call_native(&mut self, id: FunctionId, args: &[Binding]) -> Result<(), RuntimeError> {
        let native = self.native(id)?;
        let signature = native.signature();
        let (output, inputs) = args
            .split_last()
            .ok_or_else(|| invalid("native result missing"))?;
        if inputs.len() != signature.parameters.len() {
            return Err(invalid("native arity mismatch"));
        }
        let output = output.place()?;
        if output.kind != ScalarKind::for_type(signature.result.ty())? {
            return Err(invalid("invalid native output storage"));
        }
        let mut addresses = Vec::with_capacity(inputs.len());
        for (input, parameter) in inputs.iter().zip(&signature.parameters) {
            let address = input.place()?;
            if address.kind != ScalarKind::for_native(parameter.layout())?
                || !self.memory.initialized(address)?
            {
                return Err(invalid("invalid native input storage"));
            }
            if address == output && !matches!(parameter, NativeParameter::Scalar(..)) {
                return Err(invalid("native output aliases an input"));
            }
            addresses.push(address);
        }
        for (index, address) in addresses.iter().enumerate() {
            for (other_index, other) in addresses[..index].iter().enumerate() {
                if address == other
                    && !matches!(signature.parameters[index], NativeParameter::Scalar(..))
                    && !matches!(
                        signature.parameters[other_index],
                        NativeParameter::Scalar(..)
                    )
                    && (matches!(
                        signature.parameters[index],
                        NativeParameter::Mutable(_) | NativeParameter::Consuming(_)
                    ) || matches!(
                        signature.parameters[other_index],
                        NativeParameter::Mutable(_) | NativeParameter::Consuming(_)
                    ))
                {
                    return Err(invalid("overlapping mutable native arguments"));
                }
            }
        }
        // Scalar transport copies before establishing *any* native reference. Optimized MIR may
        // legitimately reuse an input's storage as the output or as another mutable argument.
        let mut scalars = addresses
            .iter()
            .zip(&signature.parameters)
            .map(|(address, parameter)| {
                if matches!(parameter, NativeParameter::Scalar(..)) {
                    self.memory.read(*address).map(Some)
                } else {
                    Ok(None)
                }
            })
            .collect::<Result<Vec<_>, RuntimeError>>()?;
        let pointers = addresses
            .iter()
            .zip(&mut scalars)
            .map(|(address, scalar)| match scalar {
                Some(value) => Ok(value.pointer()),
                None => self.memory.pointer(*address),
            })
            .collect::<Result<Vec<_>, _>>()?;
        let output_pointer = self.memory.pointer(output)?;
        // TrivialCopy result slots may be reused. Present an absent output to the C protocol,
        // and only mark it initialized after success (also when the previous result was live).
        self.memory.clear(output)?;
        let mut failure = NativeFailureState::default();
        // SAFETY: layouts, initialization, liveness and disjointness were checked above. Addresses
        // are stable; no interpreter storage access occurs until the adapter's Rust borrows end.
        unsafe { native.invoke_physical(&pointers, output_pointer, &mut failure) }?;
        if signature.result == NativeResult::Never {
            return Err(invalid("never native returned success"));
        }
        for (address, parameter) in addresses.iter().zip(&signature.parameters) {
            if matches!(parameter, NativeParameter::Consuming(_)) {
                self.memory.clear(*address)?;
            }
        }
        self.memory.mark_initialized(output)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::value::LiteralValue;

    #[test]
    fn physical_scalar_transfers_preserve_absence_and_self_moves() {
        let program = super::super::program::resolve_physical_program([]).unwrap();
        let mut interpreter = Interpreter {
            program: &program,
            memory: Memory::default(),
            limits: ReferenceInterpreterLimits::default(),
            fuel: None,
            depth: 0,
        };
        let body = Function::new(
            "transfers".into(),
            CallResultConvention::Value,
            vec![],
            vec![],
            vec![],
        );
        let source = interpreter.memory.allocate(ScalarKind::Int).unwrap();
        let destination = interpreter.memory.allocate(ScalarKind::Int).unwrap();
        let mut registers = FxHashMap::from_iter([
            (mir::ValueId::from_index(0), Binding::Place(source)),
            (mir::ValueId::from_index(1), Binding::Place(destination)),
        ]);
        let source_operand = mir::Value::Register(mir::ValueId::from_index(0));
        let destination_operand = mir::Value::Register(mir::ValueId::from_index(1));
        let span = Location::new_synthesized();
        let self_move = Operation::move_value(span, source_operand.clone(), source_operand.clone());
        assert!(
            interpreter
                .operation(&body, &[], &mut registers, &self_move, 0)
                .is_err()
        );
        interpreter.memory.write(source, Scalar::Int(42)).unwrap();
        interpreter
            .operation(&body, &[], &mut registers, &self_move, 0)
            .unwrap();
        assert_eq!(interpreter.memory.read(source).unwrap(), Scalar::Int(42));

        let replace = Operation::replace(span, source_operand, destination_operand, None);
        for old in [None, Some(Scalar::Int(7))] {
            interpreter.memory.clear(destination).unwrap();
            if let Some(old) = old {
                interpreter.memory.write(destination, old).unwrap();
            }
            interpreter.memory.write(source, Scalar::Int(42)).unwrap();
            interpreter
                .operation(&body, &[], &mut registers, &replace, 0)
                .unwrap();
            assert_eq!(
                interpreter.memory.read(destination).unwrap(),
                Scalar::Int(42)
            );
            assert_eq!(
                interpreter.memory.initialized(source).unwrap(),
                old.is_some()
            );
            if let Some(old) = old {
                assert_eq!(interpreter.memory.read(source).unwrap(), old);
            }
        }
    }

    #[test]
    fn physical_capability_gate_checks_literal_patterns() {
        for (pattern, supported) in [
            (LiteralValue::new_native(1isize), true),
            (
                LiteralValue::new_tuple(vec![LiteralValue::new_native(1isize)]),
                false,
            ),
            (LiteralValue::new_variant_tag("Some".into()), false),
        ] {
            let operation = Operation::compare_eq(
                Location::new_synthesized(),
                mir::Value::Register(mir::ValueId::from_index(0)),
                mir::Value::Pattern(Box::new(pattern)),
            );
            assert_eq!(
                Interpreter::check_operation(&operation, &mut Vec::new()).is_ok(),
                supported
            );
        }
    }
}
