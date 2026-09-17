// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Core-Wasm transport shared by generated functions and registered C entries.

use wasm_encoder::ValType;

use crate::hir::native_functions::{
    NativeFailureConvention, NativeParameter, NativeResult, NativeScalar, NativeSignature,
};

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Parameter {
    Direct(ValType),
    Indirect,
}

#[derive(Clone, Copy)]
pub(super) enum ResultKind {
    Unit,
    Direct(ValType),
    Output,
    Optional,
}

#[derive(Clone)]
pub(super) struct CallAbi {
    pub parameters: Vec<Parameter>,
    pub result: ResultKind,
    pub fallible: bool,
}

impl CallAbi {
    pub fn native(signature: &NativeSignature) -> Result<Self, String> {
        let fallible = signature.failure == NativeFailureConvention::StatusWithState;
        if (fallible
            && matches!(
                signature.result,
                NativeResult::Scalar(..) | NativeResult::Optional { .. }
            ))
            || (!fallible && signature.result == NativeResult::Never)
        {
            return Err("invalid native result transport".into());
        }
        Ok(Self {
            parameters: signature
                .parameters
                .iter()
                .map(|parameter| match parameter {
                    NativeParameter::Scalar(_, scalar) => Parameter::Direct(scalar_type(*scalar)),
                    NativeParameter::Shared(_)
                    | NativeParameter::Mutable(_)
                    | NativeParameter::Consuming(_) => Parameter::Indirect,
                })
                .collect(),
            result: match signature.result {
                NativeResult::Unit | NativeResult::Never => ResultKind::Unit,
                NativeResult::Scalar(_, scalar) => ResultKind::Direct(scalar_type(scalar)),
                NativeResult::Addressor { .. } => ResultKind::Direct(ValType::I32),
                NativeResult::Output(_) => ResultKind::Output,
                NativeResult::Optional { .. } => ResultKind::Optional,
            },
            fallible,
        })
    }

    pub fn output(&self) -> bool {
        matches!(self.result, ResultKind::Output | ResultKind::Optional)
            || (self.fallible && matches!(self.result, ResultKind::Direct(_)))
    }

    pub fn parameter_count(&self) -> usize {
        self.parameters.len() + usize::from(self.fallible) + usize::from(self.output())
    }

    pub fn params(&self) -> Vec<ValType> {
        let mut types = Vec::new();
        if self.fallible {
            types.push(ValType::I32);
        }
        types.extend(self.parameters.iter().map(|p| match p {
            Parameter::Direct(ty) => *ty,
            Parameter::Indirect => ValType::I32,
        }));
        if self.output() {
            types.push(ValType::I32);
        }
        types
    }

    pub fn results(&self) -> Option<ValType> {
        if self.fallible {
            Some(ValType::I32)
        } else {
            match self.result {
                ResultKind::Direct(ty) => Some(ty),
                ResultKind::Optional => Some(ValType::I32),
                ResultKind::Unit | ResultKind::Output => None,
            }
        }
    }

    pub fn input_local(&self, index: u32) -> u32 {
        u32::from(self.fallible) + index
    }

    pub fn output_local(&self) -> u32 {
        self.input_local(self.parameters.len() as u32)
    }
}

pub(super) fn scalar_type(scalar: NativeScalar) -> ValType {
    match scalar {
        NativeScalar::Bool | NativeScalar::Int => ValType::I32,
        NativeScalar::Float => ValType::F64,
    }
}
