// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

//! Target-independent assembly and resolution of physical MIR modules.

use std::{error::Error, fmt};

use rustc_hash::FxHashMap;

use crate::{
    define_id_type,
    hir::native_functions::NativeResult,
    mir::{
        Function, Operation, OperationKind, Value, ValueId, terminator::TerminatorKind,
        value::StaticEvidence,
    },
    module::{FunctionId, LocalFunctionId, ModuleId, SubscriptId, TraitDictionaryId, id::Id},
    types::{r#trait::TraitDictionaryEntryIndex, r#type::CallResultConvention},
};

use super::{
    BackendReadyMirArtifacts, ConstructedSubscript, PhysicalDictionaryDefinition,
    PhysicalSubscriptDefinition, PhysicalSubscriptMember, constructed_dictionary_definitions,
    constructed_subscript_definitions, evidence::try_for_each_static_evidence, physical_call_arity,
    static_dictionary_definition, static_subscript,
};

define_id_type!(
    /// Dense identity of a recursively static evidence value in one resolved physical program.
    ProgramEvidenceId
);

/// Module-qualified descriptor identity before assembly assigns a target index.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Descriptor {
    Dictionary(TraitDictionaryId),
    Function(FunctionId),
    Subscript(SubscriptId),
}

/// One hash-consed static evidence value in a resolved physical program.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum InternedStaticEvidence {
    Dictionary {
        definition: TraitDictionaryId,
        captures: Box<[ProgramEvidenceId]>,
    },
    Subscript {
        definition: SubscriptId,
        captures: Box<[ProgramEvidenceId]>,
    },
    VariantPayloadStorage(bool),
}

/// A resolved whole-program view over independently lowered physical modules.
///
/// Assembly borrows every module artifact and preserves its symbolic MIR unchanged. The view validates
/// cross-module references and provides shared lookup and static-evidence identities to executors.
pub(crate) struct ResolvedPhysicalProgram<'a> {
    modules: Box<[&'a BackendReadyMirArtifacts]>,
    static_evidence: Box<[InternedStaticEvidence]>,
    evidence_ids: FxHashMap<InternedStaticEvidence, ProgramEvidenceId>,
    descriptors: Box<[Descriptor]>,
    descriptor_ids: FxHashMap<Descriptor, u32>,
}

impl ResolvedPhysicalProgram<'_> {
    pub(crate) fn descriptor_index(&self, id: TraitDictionaryId) -> Option<u32> {
        self.reference_index(Descriptor::Dictionary(id))
    }

    pub(crate) fn reference_index(&self, id: Descriptor) -> Option<u32> {
        self.descriptor_ids.get(&id).copied()
    }

    pub(crate) fn reference_descriptor(&self, index: u32) -> Option<Descriptor> {
        self.descriptors.get(index as usize).copied()
    }

    pub(crate) fn descriptor(&self, index: u32) -> Option<&PhysicalDictionaryDefinition> {
        let Descriptor::Dictionary(id) = self.reference_descriptor(index)? else {
            return None;
        };
        self.dictionary(id)
    }

    pub(crate) fn modules(&self) -> &[&BackendReadyMirArtifacts] {
        &self.modules
    }

    pub(crate) fn module(&self, id: ModuleId) -> Option<&BackendReadyMirArtifacts> {
        self.modules
            .binary_search_by_key(&id.as_index(), |module| module.module().as_index())
            .ok()
            .map(|index| self.modules[index])
    }

    pub(crate) fn function(&self, id: FunctionId) -> Option<&Function> {
        self.module(id.module)?.get(id.function)
    }

    pub(crate) fn dictionary(
        &self,
        id: TraitDictionaryId,
    ) -> Option<&PhysicalDictionaryDefinition> {
        self.module(id.module_id)?.dictionary(id)
    }

    pub(crate) fn subscript(&self, id: SubscriptId) -> Option<&PhysicalSubscriptDefinition> {
        self.module(id.module)?.subscript(id)
    }

    pub(crate) fn subscript_member(
        &self,
        id: SubscriptId,
        mut_member: bool,
    ) -> Option<PhysicalSubscriptMember> {
        self.module(id.module)?.subscript_member(id, mut_member)
    }

    pub(crate) fn static_evidence(&self) -> &[InternedStaticEvidence] {
        &self.static_evidence
    }

    /// Resolve a symbolic compile-time evidence operand to its program-wide interned identity.
    pub(crate) fn evidence_id(&self, value: &Value) -> Option<ProgramEvidenceId> {
        evidence_value_id(&self.evidence_ids, value)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PhysicalProgramError {
    DescriptorIndexOverflow,
    DuplicateModule(ModuleId),
    UnresolvedFunction {
        owner: FunctionId,
        target: FunctionId,
    },
    InvalidCall {
        owner: FunctionId,
        target: FunctionId,
        expected: usize,
        actual: usize,
    },
    InvalidCallConvention {
        owner: FunctionId,
        target: FunctionId,
        expected: CallResultConvention,
        actual: CallResultConvention,
    },
    InvalidResultParameter {
        function: FunctionId,
    },
    UnresolvedDictionary {
        owner: FunctionId,
        dictionary: TraitDictionaryId,
    },
    InvalidDictionaryCaptureCount {
        owner: FunctionId,
        dictionary: TraitDictionaryId,
        expected: usize,
        actual: usize,
    },
    InvalidDictionaryEntryIndex {
        owner: FunctionId,
        dictionary: TraitDictionaryId,
        entry: TraitDictionaryEntryIndex,
    },
    InvalidDictionaryEntryFunction {
        dictionary: TraitDictionaryId,
        entry: TraitDictionaryEntryIndex,
        target: FunctionId,
    },
    UnresolvedSubscript {
        owner: FunctionId,
        subscript: SubscriptId,
    },
    InvalidSubscriptCaptureCount {
        owner: FunctionId,
        subscript: SubscriptId,
        expected: usize,
        actual: usize,
    },
    MissingSubscriptMember {
        owner: FunctionId,
        subscript: SubscriptId,
        mut_member: bool,
    },
    InvalidSubscriptMemberFunction {
        subscript: SubscriptId,
        mut_member: bool,
        target: FunctionId,
    },
}

impl fmt::Display for PhysicalProgramError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DescriptorIndexOverflow => {
                write!(f, "physical descriptor table exceeds u32 indexes")
            }
            Self::InvalidResultParameter { function } => write!(
                f,
                "resolved physical entry {function:?} requires exactly one trailing result parameter"
            ),
            Self::InvalidCallConvention {
                owner,
                target,
                expected,
                actual,
            } => write!(
                f,
                "resolved-program call in {owner:?} to {target:?} uses {actual:?}, expected {expected:?}"
            ),
            Self::DuplicateModule(module) => {
                write!(f, "physical module m{module} appears more than once")
            }
            Self::UnresolvedFunction { owner, target } => write!(
                f,
                "physical entry m{}:f{} refers to missing function m{}:f{}",
                owner.module, owner.function, target.module, target.function
            ),
            Self::InvalidCall {
                owner,
                target,
                expected,
                actual,
            } => write!(
                f,
                "physical call in m{}:f{} passes {actual} operands to m{}:f{}, which expects {expected}",
                owner.module, owner.function, target.module, target.function
            ),
            Self::UnresolvedDictionary { owner, dictionary } => write!(
                f,
                "physical entry m{}:f{} refers to missing dictionary m{}:i{}",
                owner.module, owner.function, dictionary.module_id, dictionary.impl_id
            ),
            Self::InvalidDictionaryCaptureCount {
                owner,
                dictionary,
                expected,
                actual,
            } => write!(
                f,
                "physical entry m{}:f{} closes dictionary m{}:i{} over {actual} captures, expected {expected}",
                owner.module, owner.function, dictionary.module_id, dictionary.impl_id
            ),
            Self::InvalidDictionaryEntryIndex {
                owner,
                dictionary,
                entry,
            } => write!(
                f,
                "physical entry m{}:f{} projects missing entry {} from dictionary m{}:i{}",
                owner.module,
                owner.function,
                entry.as_index(),
                dictionary.module_id,
                dictionary.impl_id
            ),
            Self::InvalidDictionaryEntryFunction {
                dictionary,
                entry,
                target,
            } => write!(
                f,
                "dictionary m{}:i{} entry {} refers to missing function m{}:f{}",
                dictionary.module_id,
                dictionary.impl_id,
                entry.as_index(),
                target.module,
                target.function
            ),
            Self::UnresolvedSubscript { owner, subscript } => write!(
                f,
                "physical entry m{}:f{} refers to missing subscript m{}:s{}",
                owner.module, owner.function, subscript.module, subscript.subscript
            ),
            Self::InvalidSubscriptCaptureCount {
                owner,
                subscript,
                expected,
                actual,
            } => write!(
                f,
                "physical entry m{}:f{} closes subscript m{}:s{} over {actual} captures, expected {expected}",
                owner.module, owner.function, subscript.module, subscript.subscript
            ),
            Self::MissingSubscriptMember {
                owner,
                subscript,
                mut_member,
            } => write!(
                f,
                "physical entry m{}:f{} selects missing {} member from subscript m{}:s{}",
                owner.module,
                owner.function,
                if *mut_member { "mut" } else { "ref" },
                subscript.module,
                subscript.subscript
            ),
            Self::InvalidSubscriptMemberFunction {
                subscript,
                mut_member,
                target,
            } => write!(
                f,
                "subscript m{}:s{} {} member refers to missing function m{}:f{}",
                subscript.module,
                subscript.subscript,
                if *mut_member { "mut" } else { "ref" },
                target.module,
                target.function
            ),
        }
    }
}

impl Error for PhysicalProgramError {}

/// Assemble unchanged physical module artifacts into a resolved executable program view.
pub(crate) fn resolve_physical_program<'a>(
    modules: impl IntoIterator<Item = &'a BackendReadyMirArtifacts>,
) -> Result<ResolvedPhysicalProgram<'a>, PhysicalProgramError> {
    let mut modules = modules.into_iter().collect::<Vec<_>>();
    modules.sort_by_key(|module| module.module().as_index());
    for pair in modules.windows(2) {
        if pair[0].module() == pair[1].module() {
            return Err(PhysicalProgramError::DuplicateModule(pair[0].module()));
        }
    }
    let mut program = ResolvedPhysicalProgram {
        modules: modules.into_boxed_slice(),
        static_evidence: Box::new([]),
        evidence_ids: FxHashMap::default(),
        descriptors: Box::new([]),
        descriptor_ids: FxHashMap::default(),
    };
    verify_program(&program)?;

    let descriptors = program
        .modules()
        .iter()
        .flat_map(|module| {
            module
                .dictionaries()
                .iter()
                .map(|d| Descriptor::Dictionary(d.id()))
                .chain(
                    module
                        .subscripts()
                        .iter()
                        .map(|s| Descriptor::Subscript(s.id())),
                )
                .chain((0..module.entry_count()).map(|i| {
                    Descriptor::Function(FunctionId::new(
                        module.module(),
                        LocalFunctionId::from_index(i),
                    ))
                }))
        })
        .collect::<Box<[_]>>();
    program.descriptor_ids = descriptors
        .iter()
        .enumerate()
        .map(|(index, id)| {
            Ok((
                *id,
                u32::try_from(index).map_err(|_| PhysicalProgramError::DescriptorIndexOverflow)?,
            ))
        })
        .collect::<Result<_, PhysicalProgramError>>()?;
    program.descriptors = descriptors;

    let mut interner = EvidenceInterner::default();
    for module in program.modules() {
        for function in module.entries.iter().flatten() {
            intern_function_evidence(function, &mut interner);
        }
    }
    let (static_evidence, evidence_ids) = interner.finish();
    program.static_evidence = static_evidence;
    program.evidence_ids = evidence_ids;
    Ok(program)
}

fn verify_program(program: &ResolvedPhysicalProgram) -> Result<(), PhysicalProgramError> {
    for module in program.modules() {
        for dictionary in module.dictionaries() {
            for (index, entry) in dictionary.entries().iter().enumerate() {
                if !has_function(program, entry.function()) {
                    return Err(PhysicalProgramError::InvalidDictionaryEntryFunction {
                        dictionary: dictionary.id(),
                        entry: TraitDictionaryEntryIndex::from_index(index),
                        target: entry.function(),
                    });
                }
            }
        }
        for subscript in module.subscripts() {
            for mut_member in [false, true] {
                let Some(member) = subscript.member(mut_member) else {
                    continue;
                };
                let signature = program
                    .module(member.function().module)
                    .and_then(|module| module.native_signature(member.function()));
                let wrong_access = signature.is_some_and(|signature| {
                    matches!(signature.result, NativeResult::Addressor { mutable, .. } if mutable != mut_member)
                });
                if !has_function(program, member.function()) || wrong_access {
                    return Err(PhysicalProgramError::InvalidSubscriptMemberFunction {
                        subscript: subscript.id(),
                        mut_member,
                        target: member.function(),
                    });
                }
            }
        }
        for (index, body) in module.entries.iter().enumerate() {
            let Some(body) = body else { continue };
            let owner = FunctionId::new(module.module(), LocalFunctionId::from_index(index));
            verify_function_body(program, owner, body)?;
        }
    }
    Ok(())
}

fn verify_function_body(
    program: &ResolvedPhysicalProgram,
    owner: FunctionId,
    body: &Function,
) -> Result<(), PhysicalProgramError> {
    let dictionaries = constructed_dictionary_definitions(body);
    let subscripts = constructed_subscript_definitions(body);
    for block in body.blocks() {
        let block = body.block(block);
        for operation in block.operations() {
            verify_operation(program, owner, &dictionaries, &subscripts, operation)?;
        }
        match &block.terminator().kind {
            TerminatorKind::Invoke { operation, .. } => {
                verify_operation(program, owner, &dictionaries, &subscripts, operation)?;
            }
            _ => {
                for operand in block.terminator().operands() {
                    verify_value(program, owner, operand)?;
                }
            }
        }
    }
    Ok(())
}

fn verify_operation(
    program: &ResolvedPhysicalProgram,
    owner: FunctionId,
    dictionaries: &FxHashMap<ValueId, TraitDictionaryId>,
    subscripts: &FxHashMap<ValueId, ConstructedSubscript>,
    operation: &Operation,
) -> Result<(), PhysicalProgramError> {
    for (index, operand) in operation.operands.iter().enumerate() {
        if index == 0 && matches!(operation.kind, OperationKind::BuildSubscriptEvidence { .. }) {
            verify_subscript_base(program, owner, operand)?;
        } else {
            verify_value(program, owner, operand)?;
        }
    }
    if let Some(target) = operation.kind.function_id() {
        verify_function(program, owner, target)?;
    }
    if let OperationKind::Call { ty, .. } | OperationKind::Project { ty, .. } = &operation.kind
        && let Some(Value::Function(target)) = operation.operands.first()
        && let Some(target_body) = program.function(*target)
    {
        let expected = physical_call_arity(
            target_body,
            matches!(operation.kind, OperationKind::Project { .. }),
        )
        .ok_or(PhysicalProgramError::InvalidResultParameter { function: *target })?;
        // Semantic compatibility requires adaptation, not a mismatched physical call protocol.
        if ty.result_convention != target_body.result_convention() {
            return Err(PhysicalProgramError::InvalidCallConvention {
                owner,
                target: *target,
                expected: target_body.result_convention(),
                actual: ty.result_convention,
            });
        }
        let actual = operation.operands.len() - 1;
        if actual != expected {
            return Err(PhysicalProgramError::InvalidCall {
                owner,
                target: *target,
                expected,
                actual,
            });
        }
    }
    if let OperationKind::BuildDictionary { definition, .. } = operation.kind {
        let metadata = expect_dictionary(program, owner, definition)?;
        if operation.operands.len() != metadata.capture_schema().len() {
            return Err(PhysicalProgramError::InvalidDictionaryCaptureCount {
                owner,
                dictionary: definition,
                expected: metadata.capture_schema().len(),
                actual: operation.operands.len(),
            });
        }
    }
    if let OperationKind::DictEntry { entry_index, .. } = operation.kind
        && let Some(definition) = operation
            .operands
            .first()
            .and_then(|value| static_dictionary_definition(value, dictionaries))
    {
        let metadata = expect_dictionary(program, owner, definition)?;
        if metadata.entries().get(entry_index.as_index()).is_none() {
            return Err(PhysicalProgramError::InvalidDictionaryEntryIndex {
                owner,
                dictionary: definition,
                entry: entry_index,
            });
        }
    }
    if let OperationKind::BuildSubscriptEvidence { .. } = operation.kind
        && let Some(result) = operation.result_id()
        && let Some(value) = subscripts.get(&result)
    {
        verify_subscript_capture_count(program, owner, *value)?;
    }
    if let OperationKind::BorrowSubscriptMember { mut_member, .. } = operation.kind
        && let Some(value) = operation
            .operands
            .first()
            .and_then(|value| static_subscript(value, subscripts))
    {
        let metadata = expect_subscript(program, owner, value.definition)?;
        if metadata.member(mut_member).is_none() {
            return Err(PhysicalProgramError::MissingSubscriptMember {
                owner,
                subscript: value.definition,
                mut_member,
            });
        }
    }
    Ok(())
}

fn verify_subscript_base(
    program: &ResolvedPhysicalProgram,
    owner: FunctionId,
    value: &Value,
) -> Result<(), PhysicalProgramError> {
    match value {
        Value::Subscript(definition) => {
            expect_subscript(program, owner, *definition)?;
            Ok(())
        }
        Value::Evidence(evidence) => match evidence.as_ref() {
            StaticEvidence::Subscript {
                definition,
                captures,
            } => {
                expect_subscript(program, owner, *definition)?;
                for capture in captures {
                    verify_static_evidence(program, owner, capture)?;
                }
                Ok(())
            }
            _ => verify_static_evidence(program, owner, evidence),
        },
        _ => Ok(()),
    }
}

fn verify_value(
    program: &ResolvedPhysicalProgram,
    owner: FunctionId,
    value: &Value,
) -> Result<(), PhysicalProgramError> {
    match value {
        Value::Function(target) => verify_function(program, owner, *target),
        Value::Dictionary(definition) => {
            verify_dictionary_capture_count(program, owner, *definition, 0)
        }
        Value::Subscript(definition) => verify_subscript_capture_count(
            program,
            owner,
            ConstructedSubscript {
                definition: *definition,
                capture_count: 0,
            },
        ),
        Value::Evidence(evidence) => verify_static_evidence(program, owner, evidence),
        _ => Ok(()),
    }
}

fn verify_static_evidence(
    program: &ResolvedPhysicalProgram,
    owner: FunctionId,
    evidence: &StaticEvidence,
) -> Result<(), PhysicalProgramError> {
    try_for_each_static_evidence(evidence, &mut |evidence| match evidence {
        StaticEvidence::Dictionary {
            definition,
            captures,
        } => {
            verify_dictionary_capture_count(program, owner, *definition, captures.len())?;
            Ok(())
        }
        StaticEvidence::Subscript {
            definition,
            captures,
        } => {
            verify_subscript_capture_count(
                program,
                owner,
                ConstructedSubscript {
                    definition: *definition,
                    capture_count: captures.len(),
                },
            )?;
            Ok(())
        }
        StaticEvidence::VariantPayloadStorage(_) => Ok(()),
    })
}

fn verify_function(
    program: &ResolvedPhysicalProgram,
    owner: FunctionId,
    target: FunctionId,
) -> Result<(), PhysicalProgramError> {
    if has_function(program, target) {
        Ok(())
    } else {
        Err(PhysicalProgramError::UnresolvedFunction { owner, target })
    }
}

fn has_function(program: &ResolvedPhysicalProgram, target: FunctionId) -> bool {
    program.module(target.module).is_some_and(|module| {
        module.get(target.function).is_some() || module.native_signature(target).is_some()
    })
}

fn expect_dictionary<'a>(
    program: &'a ResolvedPhysicalProgram<'_>,
    owner: FunctionId,
    dictionary: TraitDictionaryId,
) -> Result<&'a PhysicalDictionaryDefinition, PhysicalProgramError> {
    program
        .dictionary(dictionary)
        .ok_or(PhysicalProgramError::UnresolvedDictionary { owner, dictionary })
}

fn verify_dictionary_capture_count(
    program: &ResolvedPhysicalProgram,
    owner: FunctionId,
    dictionary: TraitDictionaryId,
    actual: usize,
) -> Result<(), PhysicalProgramError> {
    let definition = expect_dictionary(program, owner, dictionary)?;
    let expected = definition.capture_schema().len();
    if actual == expected {
        Ok(())
    } else {
        Err(PhysicalProgramError::InvalidDictionaryCaptureCount {
            owner,
            dictionary,
            expected,
            actual,
        })
    }
}

fn expect_subscript<'a>(
    program: &'a ResolvedPhysicalProgram<'_>,
    owner: FunctionId,
    subscript: SubscriptId,
) -> Result<&'a PhysicalSubscriptDefinition, PhysicalProgramError> {
    program
        .subscript(subscript)
        .ok_or(PhysicalProgramError::UnresolvedSubscript { owner, subscript })
}

fn verify_subscript_capture_count(
    program: &ResolvedPhysicalProgram,
    owner: FunctionId,
    value: ConstructedSubscript,
) -> Result<(), PhysicalProgramError> {
    let definition = expect_subscript(program, owner, value.definition)?;
    let expected = definition.capture_schema().len();
    if value.capture_count == expected {
        Ok(())
    } else {
        Err(PhysicalProgramError::InvalidSubscriptCaptureCount {
            owner,
            subscript: value.definition,
            expected,
            actual: value.capture_count,
        })
    }
}

#[derive(Default)]
struct EvidenceInterner {
    values: Vec<InternedStaticEvidence>,
    ids: FxHashMap<InternedStaticEvidence, ProgramEvidenceId>,
}

impl EvidenceInterner {
    fn value(&mut self, value: &Value) -> Option<ProgramEvidenceId> {
        match value {
            Value::Dictionary(definition) => {
                Some(self.intern(InternedStaticEvidence::Dictionary {
                    definition: *definition,
                    captures: Box::new([]),
                }))
            }
            Value::Subscript(definition) => Some(self.intern(InternedStaticEvidence::Subscript {
                definition: *definition,
                captures: Box::new([]),
            })),
            Value::Evidence(evidence) => Some(self.static_evidence(evidence)),
            _ => None,
        }
    }

    fn static_evidence(&mut self, evidence: &StaticEvidence) -> ProgramEvidenceId {
        let value = match evidence {
            StaticEvidence::Dictionary {
                definition,
                captures,
            } => InternedStaticEvidence::Dictionary {
                definition: *definition,
                captures: captures
                    .iter()
                    .map(|capture| self.static_evidence(capture))
                    .collect(),
            },
            StaticEvidence::Subscript {
                definition,
                captures,
            } => InternedStaticEvidence::Subscript {
                definition: *definition,
                captures: captures
                    .iter()
                    .map(|capture| self.static_evidence(capture))
                    .collect(),
            },
            StaticEvidence::VariantPayloadStorage(indirect) => {
                InternedStaticEvidence::VariantPayloadStorage(*indirect)
            }
        };
        self.intern(value)
    }

    fn intern(&mut self, value: InternedStaticEvidence) -> ProgramEvidenceId {
        if let Some(id) = self.ids.get(&value) {
            return *id;
        }
        let id = ProgramEvidenceId::from_index(self.values.len());
        self.values.push(value.clone());
        self.ids.insert(value, id);
        id
    }

    fn finish(
        self,
    ) -> (
        Box<[InternedStaticEvidence]>,
        FxHashMap<InternedStaticEvidence, ProgramEvidenceId>,
    ) {
        (self.values.into_boxed_slice(), self.ids)
    }
}

fn evidence_value_id(
    ids: &FxHashMap<InternedStaticEvidence, ProgramEvidenceId>,
    value: &Value,
) -> Option<ProgramEvidenceId> {
    let interned = match value {
        Value::Dictionary(definition) => InternedStaticEvidence::Dictionary {
            definition: *definition,
            captures: Box::new([]),
        },
        Value::Subscript(definition) => InternedStaticEvidence::Subscript {
            definition: *definition,
            captures: Box::new([]),
        },
        Value::Evidence(evidence) => interned_static_evidence(ids, evidence)?,
        _ => return None,
    };
    ids.get(&interned).copied()
}

fn interned_static_evidence(
    ids: &FxHashMap<InternedStaticEvidence, ProgramEvidenceId>,
    evidence: &StaticEvidence,
) -> Option<InternedStaticEvidence> {
    Some(match evidence {
        StaticEvidence::Dictionary {
            definition,
            captures,
        } => InternedStaticEvidence::Dictionary {
            definition: *definition,
            captures: captures
                .iter()
                .map(|capture| {
                    let interned = interned_static_evidence(ids, capture)?;
                    ids.get(&interned).copied()
                })
                .collect::<Option<_>>()?,
        },
        StaticEvidence::Subscript {
            definition,
            captures,
        } => InternedStaticEvidence::Subscript {
            definition: *definition,
            captures: captures
                .iter()
                .map(|capture| {
                    let interned = interned_static_evidence(ids, capture)?;
                    ids.get(&interned).copied()
                })
                .collect::<Option<_>>()?,
        },
        StaticEvidence::VariantPayloadStorage(indirect) => {
            InternedStaticEvidence::VariantPayloadStorage(*indirect)
        }
    })
}

fn intern_function_evidence(function: &Function, interner: &mut EvidenceInterner) {
    for block in function.blocks() {
        let block = function.block(block);
        for operation in block.operations() {
            for operand in &operation.operands {
                interner.value(operand);
            }
        }
        for operand in block.terminator().operands() {
            interner.value(operand);
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        mir::{Value, value::StaticEvidence},
        module::{LocalImplId, ModuleId, TraitDictionaryId, id::Id},
    };

    use super::{EvidenceInterner, ResolvedPhysicalProgram};

    #[test]
    fn equivalent_static_evidence_trees_share_one_program_identity() {
        let evidence = StaticEvidence::Dictionary {
            definition: TraitDictionaryId::new(ModuleId::from_index(3), LocalImplId::from_index(5)),
            captures: vec![StaticEvidence::VariantPayloadStorage(true)].into_boxed_slice(),
        };
        let mut interner = EvidenceInterner::default();
        let first = interner.static_evidence(&evidence);
        let second = interner.static_evidence(&evidence);
        assert_eq!(first, second);

        let (static_evidence, evidence_ids) = interner.finish();
        assert_eq!(
            static_evidence.len(),
            2,
            "one leaf and one closed dictionary"
        );
        let program = ResolvedPhysicalProgram {
            modules: Box::new([]),
            static_evidence,
            evidence_ids,
            descriptors: Box::new([]),
            descriptor_ids: Default::default(),
        };
        assert_eq!(
            program.evidence_id(&Value::Evidence(Box::new(evidence))),
            Some(first)
        );
    }
}
