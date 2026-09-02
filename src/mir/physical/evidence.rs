// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

//! Symbolic evidence references used by relocatable physical catalogs.

use rustc_hash::FxHashSet;

use crate::{
    mir::{
        Function, Operation, OperationKind, Value, terminator::TerminatorKind,
        value::StaticEvidence,
    },
    module::{SubscriptId, TraitDictionaryId},
};

#[derive(Default)]
pub(super) struct PhysicalEvidenceReferences {
    dictionaries: FxHashSet<TraitDictionaryId>,
    subscripts: FxHashSet<SubscriptId>,
}

impl PhysicalEvidenceReferences {
    pub(super) fn collect(functions: &[Option<Function>]) -> Self {
        let mut references = Self::default();
        for function in functions.iter().flatten() {
            references.collect_function(function);
        }
        references
    }

    pub(super) fn dictionaries(&self) -> impl Iterator<Item = TraitDictionaryId> + '_ {
        self.dictionaries.iter().copied()
    }

    pub(super) fn subscripts(&self) -> impl Iterator<Item = SubscriptId> + '_ {
        self.subscripts.iter().copied()
    }

    fn collect_function(&mut self, function: &Function) {
        for block in function.blocks() {
            let block = function.block(block);
            for operation in block.operations() {
                self.collect_operation(operation);
            }
            match &block.terminator().kind {
                TerminatorKind::Invoke { operation, .. } => self.collect_operation(operation),
                _ => {
                    for operand in block.terminator().operands() {
                        self.collect_value(operand);
                    }
                }
            }
        }
    }

    fn collect_operation(&mut self, operation: &Operation) {
        if let OperationKind::BuildDictionary { definition, .. } = operation.kind {
            self.dictionaries.insert(definition);
        }
        for operand in &operation.operands {
            self.collect_value(operand);
        }
    }

    fn collect_value(&mut self, value: &Value) {
        match value {
            Value::Dictionary(definition) => {
                self.dictionaries.insert(*definition);
            }
            Value::Subscript(definition) => {
                self.subscripts.insert(*definition);
            }
            Value::Evidence(evidence) => self.collect_static(evidence),
            _ => {}
        }
    }

    fn collect_static(&mut self, evidence: &StaticEvidence) {
        let captures = match evidence {
            StaticEvidence::Dictionary {
                definition,
                captures,
            } => {
                self.dictionaries.insert(*definition);
                captures
            }
            StaticEvidence::Subscript {
                definition,
                captures,
            } => {
                self.subscripts.insert(*definition);
                captures
            }
            StaticEvidence::VariantPayloadStorage(_) => return,
        };
        for capture in captures {
            self.collect_static(capture);
        }
    }
}

/// Visit one static evidence tree in pre-order, stopping at the first error.
pub(super) fn try_for_each_static_evidence<E>(
    evidence: &StaticEvidence,
    visit: &mut impl FnMut(&StaticEvidence) -> Result<(), E>,
) -> Result<(), E> {
    visit(evidence)?;
    let captures = match evidence {
        StaticEvidence::Dictionary { captures, .. }
        | StaticEvidence::Subscript { captures, .. } => captures,
        StaticEvidence::VariantPayloadStorage(_) => return Ok(()),
    };
    for capture in captures {
        try_for_each_static_evidence(capture, visit)?;
    }
    Ok(())
}
