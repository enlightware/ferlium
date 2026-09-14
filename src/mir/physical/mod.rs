// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

//! Physical MIR lowering, readiness verification, and whole-program resolution.

mod buffer;
mod dictionary;
mod evidence;
pub(crate) mod interpreter;
mod native;
mod native_access;
pub(crate) mod program;
mod subscript;
mod subscript_lifecycle;

use std::{
    cmp::{Ordering, Reverse},
    error::Error,
    fmt,
    slice::from_ref,
};

use rustc_hash::{FxHashMap, FxHashSet};
use ustr::Ustr;

use crate::{
    Location,
    compiler::MirArtifacts,
    hir::{
        dictionary::DictionaryReq,
        function::{ArgConvention, CallableDefinition},
        native_functions::{
            NativeContractError, NativeEntry, NativeLayout, NativeResult, NativeSignature,
        },
        value::{LiteralValue, VariantPayloadStorage},
    },
    mir::{
        BlockId, Function, Operation, OperationKind, ParameterId, ParameterKind, Value, ValueId,
        builder::FunctionBuilder,
        edit::FunctionEdit,
        pass::{
            dataflow::{Root, escaping_roots},
            known_callee::{KnownCallee, KnownCallees},
        },
        role::{MirType, ValueRoles},
        terminator::{Terminator, TerminatorKind},
        value::{ConstantId, StaticEvidence},
        verify::verify_physical_function,
    },
    module::{
        CallableOrigin, DictionaryEntryEvidence, FunctionId, LocalFunctionId, LocalImplId,
        LocalSubscriptId, ModuleEnv, ModuleId, ProjectionIndex, ResolvedValueLayout, SubscriptId,
        TraitDictionaryEntry, TraitDictionaryId, id::Id,
    },
    std::{
        buffer::buffer_element_type,
        core_traits_names::VALUE_TRAIT_NAME,
        logic::bool_type,
        math::int_type,
        option::{NativeOptionalContractError, native_optional_payload_contract_with},
        ordering::{ORDERING_EQUAL, ORDERING_GREATER},
        value::{
            ProductLayoutOrder, ProductLayoutSpec, ProductMemberLayout,
            VALUE_ALIGN_ASSOC_CONST_INDEX, VALUE_SIZE_ASSOC_CONST_INDEX, is_value_drop_function,
            product_layout_spec, value_layout_for_type, value_layout_getter_entry,
            variant_indirect_payload_type, variant_payload_offset,
            variant_payload_storage_for_payload_type, variant_tag_layout,
        },
    },
    types::{
        effects::no_effects,
        r#trait::{TraitAssociatedConstIndex, TraitDictionaryEntryIndex},
        r#type::{CallImplType, CallResultConvention, FnType, Type},
    },
};

use buffer::BufferEntry;
use dictionary::PhysicalDictionaryCatalog;
pub(crate) use dictionary::{PhysicalDictionaryDefinition, PhysicalDictionaryEntry};
use evidence::{PhysicalEvidenceReferences, try_for_each_static_evidence};
use native::{NativeRequirementError, NativeRequirements};
use subscript::PhysicalSubscriptCatalog;
pub(crate) use subscript::{PhysicalSubscriptDefinition, PhysicalSubscriptMember};

/// A physical-lowering or readiness failure.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BackendReadinessError {
    InvalidPhysicalEntry {
        owner: FunctionId,
        target: FunctionId,
    },
    UnresolvedPhysicalOperation {
        function: FunctionId,
        operation: &'static str,
    },
    InvalidProductProjection {
        function: FunctionId,
    },
    InvalidVariantPayloadProjection {
        function: FunctionId,
    },
    InvalidVariantShellStore {
        function: FunctionId,
    },
    InvalidBufferCall {
        function: FunctionId,
    },
    InvalidNativeOptionalResult {
        function: FunctionId,
        error: NativeOptionalContractError,
    },
    InvalidNativeEntry {
        function: FunctionId,
        error: NativeContractError,
    },
    NativeRequirement(NativeRequirementError),
    InvalidNativeInteriorAccess {
        function: FunctionId,
        operation: &'static str,
    },
    InvalidPhysicalCall {
        owner: FunctionId,
        target: FunctionId,
        expected: usize,
        actual: usize,
    },
    InvalidPhysicalCallConvention {
        owner: FunctionId,
        target: FunctionId,
        expected: CallResultConvention,
        actual: CallResultConvention,
    },
    InvalidPhysicalProtocol {
        function: FunctionId,
        reason: &'static str,
    },
    InvalidDictionaryDefinition {
        dictionary: TraitDictionaryId,
    },
    InvalidDictionaryEntry {
        dictionary: TraitDictionaryId,
        target: FunctionId,
    },
    UnresolvedDictionaryReference {
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
    InvalidSubscriptDefinition {
        subscript: SubscriptId,
    },
    InvalidSubscriptMember {
        subscript: SubscriptId,
        target: FunctionId,
    },
    UnresolvedSubscriptReference {
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
}

impl fmt::Display for BackendReadinessError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidPhysicalProtocol { function, reason } => write!(
                f,
                "physical entry {function:?} has an invalid execution protocol: {reason}"
            ),
            Self::InvalidPhysicalCallConvention {
                owner,
                target,
                expected,
                actual,
            } => write!(
                f,
                "physical call in {owner:?} to {target:?} uses {actual:?}, expected {expected:?}"
            ),
            Self::NativeRequirement(error) => error.fmt(f),
            Self::InvalidNativeInteriorAccess {
                function,
                operation,
            } => write!(
                f,
                "{operation} violates initialized native member access in {function:?}"
            ),
            Self::InvalidPhysicalEntry { owner, target } => write!(
                f,
                "physical entry m{}:f{} refers to unavailable entry m{}:f{}",
                owner.module, owner.function, target.module, target.function
            ),
            Self::UnresolvedPhysicalOperation {
                function,
                operation,
            } => write!(
                f,
                "physical entry m{}:f{} retains unresolved `{operation}`",
                function.module, function.function
            ),
            Self::InvalidProductProjection { function } => write!(
                f,
                "physical entry m{}:f{} contains an invalid product projection",
                function.module, function.function
            ),
            Self::InvalidVariantPayloadProjection { function } => write!(
                f,
                "physical entry m{}:f{} contains an invalid variant-payload projection",
                function.module, function.function
            ),
            Self::InvalidVariantShellStore { function } => write!(
                f,
                "physical entry m{}:f{} does not store each variant shell exactly once",
                function.module, function.function
            ),
            Self::InvalidBufferCall { function } => write!(
                f,
                "physical entry m{}:f{} contains an invalid Buffer call",
                function.module, function.function
            ),
            Self::InvalidNativeOptionalResult { function, error } => write!(
                f,
                "native entry m{}:f{} has an invalid optional-result contract: {error:?}",
                function.module, function.function,
            ),
            Self::InvalidNativeEntry { function, error } => write!(
                f,
                "native entry m{}:f{} has an invalid typed contract: {error}",
                function.module, function.function,
            ),
            Self::InvalidPhysicalCall {
                owner,
                target,
                expected,
                actual,
            } => write!(
                f,
                "physical call in m{}:f{} passes {actual} operands to m{}:f{}, which expects {expected}",
                owner.module, owner.function, target.module, target.function
            ),
            Self::InvalidDictionaryDefinition { dictionary } => write!(
                f,
                "physical dictionary m{}:i{} has invalid relocatable metadata",
                dictionary.module_id, dictionary.impl_id
            ),
            Self::InvalidDictionaryEntry { dictionary, target } => write!(
                f,
                "physical dictionary m{}:i{} refers to unavailable entry m{}:f{}",
                dictionary.module_id, dictionary.impl_id, target.module, target.function
            ),
            Self::UnresolvedDictionaryReference { owner, dictionary } => write!(
                f,
                "physical entry m{}:f{} refers to unavailable dictionary m{}:i{}",
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
            Self::InvalidSubscriptDefinition { subscript } => write!(
                f,
                "physical subscript m{}:s{} has invalid relocatable metadata",
                subscript.module, subscript.subscript
            ),
            Self::InvalidSubscriptMember { subscript, target } => write!(
                f,
                "physical subscript m{}:s{} refers to unavailable member m{}:f{}",
                subscript.module, subscript.subscript, target.module, target.function
            ),
            Self::UnresolvedSubscriptReference { owner, subscript } => write!(
                f,
                "physical entry m{}:f{} refers to unavailable subscript m{}:s{}",
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
        }
    }
}

impl Error for BackendReadinessError {}

/// Physical MIR whose readiness invariants have been checked.
pub(crate) struct BackendReadyMirArtifacts {
    module: ModuleId,
    entries: Vec<Option<Function>>,
    /// Derived after every physical transformation. Any later pass that changes function or
    /// evidence-catalog references must rebuild this map before execution.
    native_requirements: NativeRequirements,
    dictionaries: PhysicalDictionaryCatalog,
    subscripts: PhysicalSubscriptCatalog,
}

impl BackendReadyMirArtifacts {
    pub(crate) fn native_entry(&self, function: FunctionId) -> Option<&NativeEntry> {
        self.native_requirements.entries.get(&function)
    }
    pub(crate) fn native_entries(&self) -> impl Iterator<Item = (FunctionId, &NativeEntry)> {
        self.native_requirements
            .entries
            .iter()
            .map(|(&id, entry)| (id, entry))
    }

    pub(crate) fn native_layouts(
        &self,
    ) -> impl Iterator<Item = (NativeLayout, Option<(FunctionId, FunctionId)>)> + '_ {
        self.native_requirements
            .types
            .values()
            .map(|requirement| (requirement.layout, requirement.lifecycle))
    }

    pub(crate) fn module(&self) -> ModuleId {
        self.module
    }

    pub(crate) fn entry_count(&self) -> usize {
        self.entries.len()
    }

    pub(crate) fn get(&self, id: LocalFunctionId) -> Option<&Function> {
        self.entries.get(id.as_index())?.as_ref()
    }

    pub(crate) fn native_optional_payload(&self, function: FunctionId) -> Option<Type> {
        match self.native_signature(function)?.result {
            NativeResult::Optional { payload, .. } => Some(payload.ty),
            _ => None,
        }
    }

    pub(crate) fn native_signature(&self, function: FunctionId) -> Option<&NativeSignature> {
        self.native_requirements.signature(function)
    }

    /// Recheck bindings against the attached runtime, including when reusing cached artifacts.
    pub(crate) fn validate_native_runtime(
        &self,
        env: ModuleEnv<'_>,
    ) -> Result<(), BackendReadinessError> {
        self.native_requirements
            .validate_runtime(env)
            .map_err(BackendReadinessError::NativeRequirement)
    }

    pub(crate) fn dictionaries(&self) -> &[PhysicalDictionaryDefinition] {
        self.dictionaries.definitions()
    }

    pub(crate) fn dictionary_imports(&self) -> &[TraitDictionaryId] {
        self.dictionaries.imports()
    }

    pub(crate) fn dictionary(
        &self,
        id: TraitDictionaryId,
    ) -> Option<&PhysicalDictionaryDefinition> {
        self.dictionaries.definition(id)
    }

    pub(crate) fn dictionary_entry(
        &self,
        id: TraitDictionaryId,
        entry: TraitDictionaryEntryIndex,
    ) -> Option<&PhysicalDictionaryEntry> {
        self.dictionary(id)?.entries().get(entry.as_index())
    }

    pub(crate) fn subscripts(&self) -> &[PhysicalSubscriptDefinition] {
        self.subscripts.definitions()
    }

    pub(crate) fn subscript_imports(&self) -> &[SubscriptId] {
        self.subscripts.imports()
    }

    pub(crate) fn subscript(&self, id: SubscriptId) -> Option<&PhysicalSubscriptDefinition> {
        self.subscripts.definition(id)
    }

    pub(crate) fn subscript_member(
        &self,
        id: SubscriptId,
        mut_member: bool,
    ) -> Option<PhysicalSubscriptMember> {
        self.subscript(id)?.member(mut_member)
    }
}

/// Lower one module's complete optimized MIR artifact set and verify the result.
pub(crate) fn lower_physical_mir(
    module: ModuleId,
    semantic: &MirArtifacts,
    env: ModuleEnv<'_>,
    known: &KnownCallees,
) -> Result<BackendReadyMirArtifacts, BackendReadinessError> {
    assert_eq!(
        env.current.module_id(),
        module,
        "physical lowering needs the source module's environment"
    );
    let mut entries = semantic.cloned_entries();
    let helper_base = FunctionId::new(module, LocalFunctionId::from_index(entries.len()));
    let mut lowerer = PhysicalLowerer::new(helper_base, env, known);
    let buffer_entries = buffer::entries(env, known);
    for (index, specialization) in semantic.specializations().iter().enumerate() {
        let local = LocalFunctionId::from_index(semantic.len() + index);
        lowerer
            .originals
            .insert(FunctionId::new(module, local), specialization.original);
    }
    // Populate retained addressors first so later projections reuse their original identities.
    for (index, entry) in entries.iter_mut().enumerate() {
        if entry.is_some() {
            continue;
        }
        if let Some(source) = env
            .current
            .get_function_by_id(LocalFunctionId::from_index(index))
            && let CallableOrigin::StructuralFieldAddressor { field_index } = source.origin
        {
            let function = FunctionId::new(module, LocalFunctionId::from_index(index));
            let signature = &source.definition.ty_scheme.ty;
            let [receiver] = signature.args.as_slice() else {
                return Err(BackendReadinessError::InvalidProductProjection { function });
            };
            let spec = product_layout_spec(receiver.ty, Location::new_synthesized(), &env)
                .ok_or(BackendReadinessError::InvalidProductProjection { function })?;
            if spec
                .members
                .get(field_index.as_index())
                .is_none_or(|member| member.ty != signature.ret)
            {
                return Err(BackendReadinessError::InvalidProductProjection { function });
            }
            let key = ProductAddressorKey {
                aggregate_ty: receiver.ty,
                field_index,
            };
            let mut body = build_product_addressor(&key, &spec, index, known, env);
            body.name = env
                .current
                .get_function_name_by_id(function.function)
                .unwrap();
            let requirements = source
                .definition
                .ty_scheme
                .extra_parameters(env)
                .requirements;
            if body.parameters().len() != requirements.len() + 2
                || !body
                    .parameters()
                    .iter()
                    .zip(&requirements)
                    .all(|(parameter, requirement)| {
                        parameter.ty == requirement.to_dict_type_in_env(&env)
                    })
            {
                return Err(BackendReadinessError::InvalidProductProjection { function });
            }
            lowerer
                .helper_ids
                .entry(PhysicalHelperKey::Product(key))
                .or_insert(function);
            *entry = Some(body);
        }
    }
    for (index, entry) in entries.iter_mut().enumerate() {
        if let Some(body) = entry.take() {
            let local = LocalFunctionId::from_index(index);
            let original = semantic
                .specialization(local)
                .map_or(FunctionId::new(module, local), |specialization| {
                    specialization.original
                });
            *entry = Some(lowerer.lower_body(FunctionId::new(module, local), original, body)?);
        } else if let Some(&kind) =
            buffer_entries.get(&FunctionId::new(module, LocalFunctionId::from_index(index)))
        {
            *entry = Some(lowerer.lower_buffer_entry(
                FunctionId::new(module, LocalFunctionId::from_index(index)),
                kind,
            )?);
        }
    }
    entries.extend(lowerer.helpers.into_iter().map(Some));
    prepare_physical_mir(entries, semantic, env, known)
}

/// Rebuild process-local bindings and derived catalogs, then verify lowered or restored bodies.
pub(crate) fn prepare_physical_mir(
    entries: Vec<Option<Function>>,
    semantic: &MirArtifacts,
    env: ModuleEnv<'_>,
    known: &KnownCallees,
) -> Result<BackendReadyMirArtifacts, BackendReadinessError> {
    let module = env.current.module_id();
    let helper_base = FunctionId::new(module, LocalFunctionId::from_index(semantic.entry_count()));
    let buffer_entries = buffer::entries(env, known);
    let references = PhysicalEvidenceReferences::collect(&entries);
    let dictionaries =
        PhysicalDictionaryCatalog::from_module(module, env.current, env, &references);
    let subscripts = PhysicalSubscriptCatalog::from_module(module, env.current, env, &references);
    let native_signatures =
        collect_native_signatures(&entries, &dictionaries, &subscripts, env, &buffer_entries)?;
    let native_requirements = NativeRequirements::collect(&entries, &native_signatures, env)
        .map_err(BackendReadinessError::NativeRequirement)?;
    for (index, body) in entries.iter().enumerate() {
        if let Some(body) = body {
            let id = FunctionId::new(module, LocalFunctionId::from_index(index));
            let original = semantic
                .specialization(id.function)
                .map_or(id, |specialization| specialization.original);
            native_access::verify(
                body,
                id,
                original,
                helper_base,
                &native_signatures,
                &buffer_entries,
                env,
            )?;
        }
    }
    let artifacts = BackendReadyMirArtifacts {
        module,
        entries,
        native_requirements,
        dictionaries,
        subscripts,
    };
    verify_physical_mir(&artifacts, env)?;
    Ok(artifacts)
}

/// Collect transport/layout contracts under the original IDs for declared and referenced natives,
/// including evidence entries and first-class references. NativeRequirements separately captures
/// their matching runtime bindings.
// TODO: Verify indirect script-call failure transport once machine signatures are available.
fn collect_native_signatures(
    entries: &[Option<Function>],
    dictionaries: &PhysicalDictionaryCatalog,
    subscripts: &PhysicalSubscriptCatalog,
    env: ModuleEnv<'_>,
    buffer_entries: &FxHashMap<FunctionId, BufferEntry>,
) -> Result<FxHashMap<FunctionId, NativeSignature>, BackendReadinessError> {
    let mut referenced = FxHashSet::default();
    // Declared entries remain artifact roots: an embedder can call them even without a MIR use.
    for (index, function) in env.current.functions.iter().enumerate() {
        if matches!(function.origin, CallableOrigin::Native { .. }) {
            referenced.insert(FunctionId::new(
                env.current.module_id(),
                LocalFunctionId::from_index(index),
            ));
        }
    }
    for body in entries.iter().flatten() {
        body.visit_function_ids(|function| {
            referenced.insert(function);
        });
    }
    for dictionary in dictionaries.definitions() {
        for entry in dictionary.entries() {
            referenced.insert(entry.function());
        }
    }
    for subscript in subscripts.definitions() {
        for mut_member in [false, true] {
            if let Some(member) = subscript.member(mut_member) {
                referenced.insert(member.function());
            }
        }
    }
    // Imported evidence is not an opaque escape hatch for an incompatible native entry.
    for dictionary in dictionaries.imports() {
        if let Some(implementation) = env
            .module_by_id(dictionary.module_id)
            .and_then(|module| module.get_impl_data(dictionary.impl_id))
        {
            for index in 0..implementation.dictionary_value.entry_count() {
                let TraitDictionaryEntry::Function(function) = implementation
                    .dictionary_value
                    .entry(TraitDictionaryEntryIndex::from_index(index));
                referenced.insert(FunctionId::new(dictionary.module_id, function));
            }
        }
    }
    for subscript in subscripts.imports() {
        if let Some(definition) = env
            .module_by_id(subscript.module)
            .and_then(|module| module.get_subscript_by_id(subscript.subscript))
        {
            for member in [&definition.ref_member, &definition.mut_member]
                .into_iter()
                .flatten()
            {
                referenced.insert(FunctionId::new(subscript.module, member.function));
            }
        }
    }

    let mut results = FxHashMap::default();
    let mut referenced = referenced.into_iter().collect::<Vec<_>>();
    referenced.sort_by_key(|function| (function.module.as_index(), function.function.as_index()));
    for function in referenced {
        // These identities have physical bodies in their owning module. Program assembly must
        // resolve them to those bodies, never fall back to the boxed callback.
        if buffer_entries.contains_key(&function) {
            if function.module == env.current.module_id()
                && entries
                    .get(function.function.as_index())
                    .and_then(Option::as_ref)
                    .is_none()
            {
                return Err(BackendReadinessError::InvalidBufferCall { function });
            }
            continue;
        }
        let Some(module) = env.module_by_id(function.module) else {
            continue;
        };
        let Some(native) = module.get_function_by_id(function.function) else {
            continue;
        };
        if !matches!(native.origin, CallableOrigin::Native { .. }) {
            continue;
        }
        native_optional_payload_contract_with(
            native.definition.ty_scheme.ty.ret,
            native.code.native_optional_payload_type(),
            |named| {
                env.try_type_def(named.def).map(|definition| {
                    definition.instantiated_shape_with_effects(&named.params, &named.effect_params)
                })
            },
        )
        .map_err(|error| BackendReadinessError::InvalidNativeOptionalResult { function, error })?;
        let entry = native
            .code
            .native_entry()
            .ok_or(BackendReadinessError::NativeRequirement(
                NativeRequirementError::MissingEntry(function),
            ))?;
        let signature = {
            entry
                .signature()
                .validate(&native.definition)
                .map_err(|error| BackendReadinessError::InvalidNativeEntry { function, error })?;
            entry.signature().clone()
        };
        results.insert(function, signature);
    }
    Ok(results)
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct ProductAddressorKey {
    aggregate_ty: Type,
    field_index: ProjectionIndex,
}

#[derive(Clone, PartialEq, Eq, Hash)]
enum PhysicalHelperKey {
    Product(ProductAddressorKey),
    BufferDrop {
        buffer_ty: Type,
    },
    // Allocation follows the representation decision carried by the shell operation itself, so
    // retain it in the key rather than assuming two otherwise-equal shell sites agree. Addressors
    // recompute their decision canonically from the aggregate and payload types instead.
    VariantPayloadAllocation {
        variant_ty: Type,
        payload_ty: Type,
        storage: Option<VariantPayloadStorage>,
    },
    VariantPayloadAddressor {
        variant_ty: Type,
        payload_ty: Type,
    },
    VariantPayloadRelease {
        variant_ty: Type,
        payload_ty: Type,
    },
}

#[derive(Clone)]
struct VariantPayloadProjection {
    block: BlockId,
    operation_index: usize,
    operation: Operation,
    variant_ty: Type,
    storage: Option<VariantPayloadStorage>,
}

#[derive(Clone)]
struct VariantAllocationCleanup {
    active: Value,
    base_slot: Value,
    variant_ty: Type,
    payload_ty: Type,
    span: Location,
    depth: usize,
}

struct PhysicalLowerer<'a> {
    helper_base: FunctionId,
    env: ModuleEnv<'a>,
    known: &'a KnownCallees,
    helper_ids: FxHashMap<PhysicalHelperKey, FunctionId>,
    helpers: Vec<Function>,
    originals: FxHashMap<FunctionId, FunctionId>,
}

impl<'a> PhysicalLowerer<'a> {
    fn new(helper_base: FunctionId, env: ModuleEnv<'a>, known: &'a KnownCallees) -> Self {
        Self {
            helper_base,
            env,
            known,
            helper_ids: FxHashMap::default(),
            helpers: Vec::new(),
            originals: FxHashMap::default(),
        }
    }

    fn lower_body(
        &mut self,
        function: FunctionId,
        original: FunctionId,
        mut body: Function,
    ) -> Result<Function, BackendReadinessError> {
        let (lowered, allocation_cleanups) =
            self.lower_variant_shell_allocations(function, body)?;
        body = lowered;
        let product_candidates = body
            .blocks()
            .flat_map(|block| {
                body.block(block)
                    .operations()
                    .iter()
                    .enumerate()
                    .filter(|(_, operation)| {
                        matches!(
                            operation.kind,
                            OperationKind::Subfield {
                                variant_payload: false,
                                ..
                            }
                        )
                    })
                    .map(move |(index, operation)| (block, index, operation.clone()))
            })
            .collect::<Vec<_>>();
        let variant_candidates = variant_payload_projections(function, &body, self.env)?;

        enum Projection {
            Product(BlockId, usize, Operation),
            Variant(usize),
        }
        let mut projections = product_candidates
            .into_iter()
            .map(|(block, index, operation)| Projection::Product(block, index, operation))
            .chain((0..variant_candidates.len()).map(Projection::Variant))
            .collect::<Vec<_>>();
        projections.sort_by_key(|projection| match projection {
            Projection::Product(block, index, _) => (block.as_index(), *index),
            Projection::Variant(index) => {
                let candidate = &variant_candidates[*index];
                (candidate.block.as_index(), candidate.operation_index)
            }
        });

        let mut edit = FunctionEdit::new(body);
        for projection in projections.into_iter().rev() {
            match projection {
                Projection::Product(block, index, operation) => {
                    self.lower_product_projection(function, &mut edit, block, index, operation)?;
                }
                Projection::Variant(index) => self.lower_variant_payload_projection(
                    function,
                    &mut edit,
                    &variant_candidates[index],
                )?,
            }
        }
        self.lower_buffer_calls(function, &mut edit)?;
        subscript_lifecycle::lower_members(&mut edit);
        if let Some((base, variant_ty, payload_ty)) = value_drop_variant(original, &edit, self.env)
        {
            self.release_variant_on_value_drop_return(&mut edit, base, variant_ty, payload_ty);
        }
        self.lower_incomplete_variant_allocation_cleanup(&mut edit, &allocation_cleanups);
        if !variant_candidates.is_empty() || !allocation_cleanups.is_empty() {
            edit.reorder_blocks_in_reverse_postorder();
        }
        Ok(edit.finish_unverified())
    }

    fn buffer_callee(&self, operation: &Operation) -> Option<KnownCallee> {
        if !matches!(operation.kind, OperationKind::Call { .. }) {
            return None;
        }
        let Some(Value::Function(callee)) = operation.operands.first() else {
            return None;
        };
        self.known
            .resolve(*callee, |id| self.originals.get(&id).copied())
            .filter(|callee| callee.is_buffer())
    }

    fn lower_buffer_calls(
        &mut self,
        function: FunctionId,
        edit: &mut FunctionEdit,
    ) -> Result<(), BackendReadinessError> {
        enum Candidate {
            Call(KnownCallee, Operation),
            Drop(Operation),
        }

        let mut candidates = Vec::new();
        for block in edit.blocks().collect::<Vec<_>>() {
            if let TerminatorKind::Invoke { operation, .. } = &edit.block(block).terminator.kind
                && self.buffer_callee(operation).is_some()
            {
                return Err(BackendReadinessError::InvalidBufferCall { function });
            }
            for (index, operation) in edit.block(block).operations.iter().enumerate() {
                let candidate = if let Some(callee) = self.buffer_callee(operation) {
                    Candidate::Call(callee, operation.clone())
                } else {
                    match operation.kind {
                        // Lifecycle dispatch may obtain its callee through a dictionary place, so
                        // recognize Buffer drop from the operation's semantic type instead.
                        OperationKind::Drop { ty } if buffer_element_type(ty).is_some() => {
                            Candidate::Drop(operation.clone())
                        }
                        _ => continue,
                    }
                };
                candidates.push((block, index, candidate));
            }
        }

        for (block, index, candidate) in candidates.into_iter().rev() {
            match candidate {
                Candidate::Call(KnownCallee::BufferDrop, mut operation) => {
                    let buffer_ty = buffer_call_type(&operation, 1, function)?.fn_ty.args[0].ty;
                    let element_ty = buffer_element_type(buffer_ty)
                        .ok_or(BackendReadinessError::InvalidBufferCall { function })?;
                    operation.operands[0] =
                        Value::Function(self.intern_buffer_drop(buffer_ty, element_ty));
                    edit.replace_operation_sequence(block, index, [operation]);
                }
                Candidate::Call(callee, operation) => {
                    let replacement = self.expand_buffer_call(function, callee, operation, edit)?;
                    edit.replace_operation_sequence(block, index, replacement);
                }
                Candidate::Drop(mut operation) => {
                    let OperationKind::Drop { ty: buffer_ty } = operation.kind else {
                        unreachable!()
                    };
                    let element_ty = buffer_element_type(buffer_ty)
                        .ok_or(BackendReadinessError::InvalidBufferCall { function })?;
                    operation.operands[1] =
                        Value::Function(self.intern_buffer_drop(buffer_ty, element_ty));
                    operation.operands = operation.operands[..2].to_vec().into_boxed_slice();
                    edit.replace_operation_sequence(block, index, [operation]);
                }
            }
        }
        Ok(())
    }

    fn intern_buffer_drop(&mut self, buffer_ty: Type, element_ty: Type) -> FunctionId {
        let key = PhysicalHelperKey::BufferDrop { buffer_ty };
        if let Some(id) = self.helper_ids.get(&key) {
            return *id;
        }
        let id = self.next_helper_id();
        let body = build_buffer_drop(buffer_ty, element_ty, self.helpers.len(), self.env);
        self.helper_ids.insert(key, id);
        self.helpers.push(body);
        id
    }

    fn expand_buffer_call(
        &self,
        function: FunctionId,
        callee: KnownCallee,
        operation: Operation,
        edit: &mut FunctionEdit,
    ) -> Result<Vec<Operation>, BackendReadinessError> {
        let expected = match callee {
            KnownCallee::BufferSlot | KnownCallee::BufferWithCapacity => 3,
            KnownCallee::BufferMove => 2,
            KnownCallee::BufferMoveInto => 5,
            KnownCallee::BufferTake => 3,
            KnownCallee::BufferDrop => unreachable!(),
            _ => unreachable!("only Buffer callees reach Buffer expansion"),
        };
        let call_ty = buffer_call_type(&operation, expected, function)?;
        let arguments = &operation.operands[1..=expected];
        let destination = operation.operands[expected + 1].clone();
        let span = operation.span;
        let element_ty = match callee {
            KnownCallee::BufferSlot | KnownCallee::BufferTake => {
                let element_ty = buffer_argument_element_type(call_ty, 0, function)?;
                if call_ty.ret() != element_ty {
                    return Err(BackendReadinessError::InvalidBufferCall { function });
                }
                element_ty
            }
            KnownCallee::BufferWithCapacity => buffer_element_type(call_ty.ret())
                .ok_or(BackendReadinessError::InvalidBufferCall { function })?,
            KnownCallee::BufferMove => {
                let element_ty = buffer_argument_element_type(call_ty, 0, function)?;
                if buffer_argument_element_type(call_ty, 1, function)? != element_ty {
                    return Err(BackendReadinessError::InvalidBufferCall { function });
                }
                element_ty
            }
            KnownCallee::BufferMoveInto => {
                let element_ty = buffer_argument_element_type(call_ty, 0, function)?;
                if buffer_argument_element_type(call_ty, 2, function)? != element_ty {
                    return Err(BackendReadinessError::InvalidBufferCall { function });
                }
                element_ty
            }
            KnownCallee::BufferDrop => unreachable!(),
            _ => unreachable!("only Buffer callees reach Buffer expansion"),
        };
        let mut replacement = Vec::new();
        match callee {
            KnownCallee::BufferWithCapacity => {
                let total = edit_int_binary(
                    edit,
                    &mut replacement,
                    self.known.int_mul(),
                    arguments[0].clone(),
                    arguments[1].clone(),
                    span,
                );
                let total = edit_result(edit, &mut replacement, Operation::load(span, total));
                let align = edit_result(
                    edit,
                    &mut replacement,
                    Operation::load(span, arguments[2].clone()),
                );
                let allocation = edit_result(
                    edit,
                    &mut replacement,
                    Operation::runtime_alloc(span, element_ty, total, align),
                );
                let slot = edit_buffer_pointer_slot(
                    edit,
                    &mut replacement,
                    destination,
                    element_ty,
                    span,
                    self.env,
                );
                replacement.push(Operation::store(span, allocation, slot));
            }
            KnownCallee::BufferSlot => {
                let address = edit_buffer_element_address(
                    edit,
                    &mut replacement,
                    arguments[0].clone(),
                    arguments[1].clone(),
                    arguments[2].clone(),
                    element_ty,
                    self.known,
                    span,
                    self.env,
                );
                replacement.push(Operation::store(span, address, destination));
            }
            KnownCallee::BufferTake => {
                let address = edit_buffer_element_address(
                    edit,
                    &mut replacement,
                    arguments[0].clone(),
                    arguments[1].clone(),
                    arguments[2].clone(),
                    element_ty,
                    self.known,
                    span,
                    self.env,
                );
                let size = edit_result(
                    edit,
                    &mut replacement,
                    Operation::load(span, arguments[2].clone()),
                );
                replacement.push(Operation::move_bytes(
                    span,
                    element_ty,
                    address,
                    destination,
                    size,
                ));
            }
            KnownCallee::BufferMoveInto => {
                let source_element = edit_buffer_element_address(
                    edit,
                    &mut replacement,
                    arguments[0].clone(),
                    arguments[1].clone(),
                    arguments[4].clone(),
                    element_ty,
                    self.known,
                    span,
                    self.env,
                );
                let target_element = edit_buffer_element_address(
                    edit,
                    &mut replacement,
                    arguments[2].clone(),
                    arguments[3].clone(),
                    arguments[4].clone(),
                    element_ty,
                    self.known,
                    span,
                    self.env,
                );
                let size = edit_result(
                    edit,
                    &mut replacement,
                    Operation::load(span, arguments[4].clone()),
                );
                replacement.push(Operation::move_bytes(
                    span,
                    element_ty,
                    source_element,
                    target_element,
                    size,
                ));
                edit_store_unit(edit, &mut replacement, destination, span, self.env);
            }
            KnownCallee::BufferMove => {
                let source = edit_buffer_pointer_slot(
                    edit,
                    &mut replacement,
                    arguments[0].clone(),
                    element_ty,
                    span,
                    self.env,
                );
                let target = edit_buffer_pointer_slot(
                    edit,
                    &mut replacement,
                    arguments[1].clone(),
                    element_ty,
                    span,
                    self.env,
                );
                let old = edit_result(
                    edit,
                    &mut replacement,
                    Operation::load(span, target.clone()),
                );
                replacement.push(Operation::runtime_dealloc(span, old));
                replacement.push(Operation::clear(span, target.clone()));
                replacement.push(Operation::move_value(span, source.clone(), target));
                // A capacity-zero Buffer has no addressable slot, so the ABI deliberately uses
                // the canonical zero-byte placeholder layout instead of `A`'s alignment.
                let zero = edit_int_constant(edit, 0, self.env);
                let one = edit_int_constant(edit, 1, self.env);
                let empty = edit_result(
                    edit,
                    &mut replacement,
                    Operation::runtime_alloc(span, element_ty, zero, one),
                );
                replacement.push(Operation::store(span, empty, source));
                edit_store_unit(edit, &mut replacement, destination, span, self.env);
            }
            KnownCallee::BufferDrop => unreachable!(),
            _ => unreachable!("only Buffer callees reach Buffer expansion"),
        }
        Ok(replacement)
    }

    fn lower_product_projection(
        &mut self,
        function: FunctionId,
        edit: &mut FunctionEdit,
        block: BlockId,
        operation_index: usize,
        operation: Operation,
    ) -> Result<(), BackendReadinessError> {
        let OperationKind::Subfield {
            ty: field_ty,
            product: Some(product),
            ..
        } = &operation.kind
        else {
            return Err(BackendReadinessError::InvalidProductProjection { function });
        };
        let field_index = constant_index(&operation.operands[1], edit)
            .ok_or(BackendReadinessError::InvalidProductProjection { function })?;
        let spec = product_layout_spec(product.aggregate_ty, operation.span, &self.env)
            .ok_or(BackendReadinessError::InvalidProductProjection { function })?;
        let Some(member) = spec.members.get(field_index.as_index()).copied() else {
            return Err(BackendReadinessError::InvalidProductProjection { function });
        };
        if member.ty != *field_ty {
            return Err(BackendReadinessError::InvalidProductProjection { function });
        }
        let expected_witnesses = spec.dynamic_member_layouts();
        if expected_witnesses.as_slice() != product.layout_witness_tys.as_ref() {
            return Err(BackendReadinessError::InvalidProductProjection { function });
        }

        let result = operation
            .result_id()
            .ok_or(BackendReadinessError::InvalidProductProjection { function })?;
        if let Some(offset) = spec.static_field_offset(field_index) {
            let offset = isize::try_from(offset)
                .map_err(|_| BackendReadinessError::InvalidProductProjection { function })?;
            let constant =
                edit.add_constant(int_type(), LiteralValue::new_native(offset), &self.env);
            let base = operation.operands[0].clone();
            let offset = Value::Constant(constant);
            let mut replacement = Operation::address_offset(
                operation.span,
                base,
                offset,
                *field_ty,
                Some(field_index),
            );
            replacement.assign_result_id(Some(result));
            edit.replace_operation_sequence(block, operation_index, [replacement]);
            return Ok(());
        }

        let key = ProductAddressorKey {
            aggregate_ty: product.aggregate_ty,
            field_index,
        };
        let helper = self.intern_product_addressor(key, &spec);
        let mut out_operation = Operation::alloca_place(operation.span, *field_ty);
        let out = edit
            .assign_new_result(&mut out_operation)
            .expect("alloca_place produces a place");
        let call_ty = product_addressor_call_type(product.aggregate_ty, *field_ty);
        let mut arguments = operation.operands[2..].to_vec();
        arguments.push(operation.operands[0].clone());
        arguments.push(out.clone());
        let call = Operation::call(operation.span, Value::Function(helper), arguments, call_ty);
        let mut load = Operation::load(operation.span, out);
        load.assign_result_id(Some(result));
        edit.replace_operation_sequence(block, operation_index, [out_operation, call, load]);
        Ok(())
    }

    fn lower_variant_payload_projection(
        &mut self,
        function: FunctionId,
        edit: &mut FunctionEdit,
        candidate: &VariantPayloadProjection,
    ) -> Result<(), BackendReadinessError> {
        let OperationKind::Subfield {
            ty: payload_ty,
            variant_payload: true,
            has_layout_witness,
            ..
        } = candidate.operation.kind
        else {
            return Err(BackendReadinessError::InvalidVariantPayloadProjection { function });
        };
        let static_layout =
            value_layout_for_type(payload_ty, candidate.operation.span, &self.env).ok();
        if has_layout_witness != static_layout.is_none() {
            return Err(BackendReadinessError::InvalidVariantPayloadProjection { function });
        }
        let result = candidate
            .operation
            .result_id()
            .ok_or(BackendReadinessError::InvalidVariantPayloadProjection { function })?;
        if candidate.storage == Some(VariantPayloadStorage::Inline)
            && let Some(layout) = static_layout
        {
            let offset = isize::try_from(variant_payload_offset(layout.align))
                .map_err(|_| BackendReadinessError::InvalidVariantPayloadProjection { function })?;
            let offset = edit.add_constant(int_type(), LiteralValue::new_native(offset), &self.env);
            let mut replacement = Operation::address_offset(
                candidate.operation.span,
                candidate.operation.operands[0].clone(),
                Value::Constant(offset),
                payload_ty,
                None,
            );
            replacement.assign_result_id(Some(result));
            edit.replace_operation_sequence(
                candidate.block,
                candidate.operation_index,
                [replacement],
            );
            return Ok(());
        }
        let helper = self.intern_variant_payload_addressor(
            candidate.variant_ty,
            payload_ty,
            candidate.storage,
            static_layout,
        );
        let mut out_operation = Operation::alloca_place(candidate.operation.span, payload_ty);
        let out = edit
            .assign_new_result(&mut out_operation)
            .expect("alloca_place produces a place");
        let mut arguments = candidate.operation.operands[2..].to_vec();
        arguments.push(candidate.operation.operands[0].clone());
        arguments.push(out.clone());
        let call = Operation::call(
            candidate.operation.span,
            Value::Function(helper),
            arguments,
            variant_payload_addressor_call_type(candidate.variant_ty, payload_ty),
        );
        let mut load = Operation::load(candidate.operation.span, out);
        load.assign_result_id(Some(result));
        edit.replace_operation_sequence(
            candidate.block,
            candidate.operation_index,
            [out_operation, call, load],
        );
        Ok(())
    }

    fn lower_variant_shell_allocations(
        &mut self,
        function: FunctionId,
        body: Function,
    ) -> Result<(Function, Vec<VariantAllocationCleanup>), BackendReadinessError> {
        let variants = body
            .blocks()
            .flat_map(|block| body.block(block).operations())
            .filter_map(|operation| {
                let OperationKind::Variant { .. } = operation.kind else {
                    return None;
                };
                Some((operation.result_id()?, operation.clone()))
            })
            .collect::<FxHashMap<_, _>>();
        if variants.is_empty() {
            return Ok((body, Vec::new()));
        }

        let mut stores = Vec::new();
        let mut stored_shells = FxHashSet::default();
        let mut inspect = |block, operation_index, operation: &Operation, allow_store| {
            for (operand_index, operand) in operation.operands.iter().enumerate() {
                let Value::Register(result) = operand else {
                    continue;
                };
                let Some(shell) = variants.get(result) else {
                    continue;
                };
                if allow_store
                    && matches!(operation.kind, OperationKind::Store)
                    && operand_index == 0
                    && stored_shells.insert(*result)
                {
                    stores.push((block, operation_index, shell.clone(), operation.clone()));
                } else {
                    return Err(BackendReadinessError::InvalidVariantShellStore { function });
                }
            }
            Ok(())
        };
        for block in body.blocks() {
            for (index, operation) in body.block(block).operations().iter().enumerate() {
                inspect(block, index, operation, true)?;
            }
            if let TerminatorKind::Invoke { operation, .. } = &body.block(block).terminator().kind {
                // Variant shells are source-infallible values and must be transferred by an
                // ordinary Store. Refuse an invoke operand instead of manufacturing an invalid
                // operation index for the splice below.
                inspect(block, 0, operation, false)?;
            } else if body
                .block(block)
                .terminator()
                .operands()
                .iter()
                .any(|operand| {
                    matches!(operand, Value::Register(result) if variants.contains_key(result))
                })
            {
                return Err(BackendReadinessError::InvalidVariantShellStore { function });
            }
        }
        if stored_shells.len() != variants.len() {
            return Err(BackendReadinessError::InvalidVariantShellStore { function });
        }
        let has_error_exit = body.blocks().any(|block| {
            matches!(
                body.block(block).terminator().kind,
                TerminatorKind::PropagateError
            )
        });
        let (_, bindings) = escaping_roots(&body, &|_| false);
        let parameters = body.parameters().to_vec();
        let mut edit = FunctionEdit::new(body);
        let mut cleanups = Vec::new();
        let mut cleanup_flag_values = None;
        let mut cleanup_prologue = Vec::new();

        for (block, index, shell, store) in stores.into_iter().rev() {
            let OperationKind::Variant {
                metadata,
                storage,
                has_layout_witness,
                ..
            } = &shell.kind
            else {
                unreachable!()
            };
            if *storage == Some(VariantPayloadStorage::Inline) {
                continue;
            }
            let static_layout =
                value_layout_for_type(metadata.payload_ty, shell.span, &self.env).ok();
            if *has_layout_witness != static_layout.is_none() {
                return Err(BackendReadinessError::InvalidVariantPayloadProjection { function });
            }
            let helper = self.intern_variant_payload_allocation(
                metadata.ty,
                metadata.payload_ty,
                *storage,
                static_layout,
            );
            let base = store.operands[1].clone();
            let mut operations = vec![store];
            let mut result_operation = Operation::alloca(shell.span, Type::unit());
            let result = edit
                .assign_new_result(&mut result_operation)
                .expect("alloca produces a place");
            operations.push(result_operation);
            let mut arguments = Vec::new();
            if *has_layout_witness {
                arguments.push(
                    shell
                        .operands
                        .last()
                        .cloned()
                        .expect("layout witness is present"),
                );
            }
            arguments.extend([base.clone(), result]);
            operations.push(Operation::call(
                shell.span,
                Value::Function(helper),
                arguments,
                variant_payload_helper_call_type(metadata.ty),
            ));

            // An ordinary local's semantic cleanup calls its selected `Value::drop`, which owns
            // representation release too. A return place belongs to the caller and is not part of
            // the callee's local cleanup, so a partial construction records its allocation here.
            if has_error_exit
                && let Some(Root::Parameter(parameter)) = bindings.root_of(&base)
                && parameters[parameter.as_index()].kind == ParameterKind::Return
            {
                let (false_value, true_value) = cleanup_flag_values.get_or_insert_with(|| {
                    (
                        Value::Constant(bool_constant(&mut edit, false, self.env)),
                        Value::Constant(bool_constant(&mut edit, true, self.env)),
                    )
                });
                let depth = bindings
                    .depth_of(&base)
                    .ok_or(BackendReadinessError::InvalidVariantPayloadProjection { function })?;
                let mut active_operation = Operation::alloca(shell.span, bool_type());
                let active = edit
                    .assign_new_result(&mut active_operation)
                    .expect("alloca produces a place");
                let mut base_operation = Operation::alloca_place(shell.span, metadata.ty);
                let base_slot = edit
                    .assign_new_result(&mut base_operation)
                    .expect("alloca_place produces a place");
                cleanup_prologue.extend([
                    active_operation,
                    Operation::store(shell.span, false_value.clone(), active.clone()),
                    base_operation,
                ]);
                operations.push(Operation::store(shell.span, base, base_slot.clone()));
                operations.push(Operation::store(
                    shell.span,
                    true_value.clone(),
                    active.clone(),
                ));
                cleanups.push(VariantAllocationCleanup {
                    active,
                    base_slot,
                    variant_ty: metadata.ty,
                    payload_ty: metadata.payload_ty,
                    span: shell.span,
                    depth,
                });
            }
            // Keep allocation adjacent to the shell store. Once Store establishes the shell's drop
            // flag, no failing operation can intervene before its representation resource exists;
            // ordinary local cleanup can therefore always reach `Value::drop` and release it.
            edit.block_mut(block)
                .operations
                .splice(index..=index, operations);
        }
        cleanups.sort_by_key(|cleanup| Reverse(cleanup.depth));
        // Recorded store indices refer to the original body. Prepending cleanup storage while
        // processing those stores would shift entry-block indices and splice at the wrong site.
        edit.block_mut(edit.entry())
            .operations
            .splice(0..0, cleanup_prologue);
        Ok((edit.finish_unverified(), cleanups))
    }

    fn release_variant_on_value_drop_return(
        &mut self,
        edit: &mut FunctionEdit,
        base: Value,
        variant_ty: Type,
        payload_ty: Type,
    ) {
        let helper = self.intern_variant_payload_release(variant_ty, payload_ty);
        let exits = edit
            .blocks()
            .filter(|block| matches!(edit.block(*block).terminator.kind, TerminatorKind::Return))
            .collect::<Vec<_>>();
        for block in exits {
            let span = edit.block(block).terminator.span;
            // Every semantic payload branch reaches this return after dropping the initialized
            // payload. That drop clears the payload leaf, not the shell/tag initialization flag, so
            // the release helper can still inspect the representation before the caller's whole-
            // variant `drop` operation finally consumes the shell.
            let operations =
                variant_payload_release_call(edit, helper, base.clone(), variant_ty, span);
            edit.block_mut(block).operations.extend(operations);
        }
    }

    fn lower_incomplete_variant_allocation_cleanup(
        &mut self,
        edit: &mut FunctionEdit,
        cleanups: &[VariantAllocationCleanup],
    ) {
        if cleanups.is_empty() {
            return;
        }
        let exits = edit
            .blocks()
            .filter(|block| {
                matches!(
                    edit.block(*block).terminator.kind,
                    TerminatorKind::PropagateError
                )
            })
            .collect::<Vec<_>>();
        let false_value = Value::Constant(bool_constant(edit, false, self.env));
        for exit in exits {
            let span = edit.block(exit).terminator.span;
            let mut next = edit.add_block(Terminator::propagate_error(span));
            // `cleanups` is deepest-first. Building the chain backwards preserves that execution
            // order, so no containing allocation is freed before an address stored inside it.
            for cleanup in cleanups.iter().rev() {
                let release = edit.add_block(Terminator::goto(cleanup.span, next));
                let base = append_edit_result(
                    edit,
                    release,
                    Operation::load(cleanup.span, cleanup.base_slot.clone()),
                );
                let helper =
                    self.intern_variant_payload_release(cleanup.variant_ty, cleanup.payload_ty);
                let mut operations = variant_payload_release_call(
                    edit,
                    helper,
                    base,
                    cleanup.variant_ty,
                    cleanup.span,
                );
                operations.push(Operation::store(
                    cleanup.span,
                    false_value.clone(),
                    cleanup.active.clone(),
                ));
                edit.block_mut(release).operations.extend(operations);

                let check = edit.add_block(Terminator::goto(cleanup.span, next));
                let active = append_edit_result(
                    edit,
                    check,
                    Operation::load(cleanup.span, cleanup.active.clone()),
                );
                edit.block_mut(check).terminator =
                    Terminator::cond_br(cleanup.span, active, release, next);
                next = check;
            }
            edit.block_mut(exit).terminator = Terminator::goto(span, next);
        }
    }

    fn intern_variant_payload_allocation(
        &mut self,
        variant_ty: Type,
        payload_ty: Type,
        storage: Option<VariantPayloadStorage>,
        static_layout: Option<ResolvedValueLayout>,
    ) -> FunctionId {
        let key = PhysicalHelperKey::VariantPayloadAllocation {
            variant_ty,
            payload_ty,
            storage,
        };
        if let Some(id) = self.helper_ids.get(&key) {
            return *id;
        }
        let id = self.next_helper_id();
        let body = build_variant_payload_allocation(
            variant_ty,
            payload_ty,
            storage,
            static_layout,
            self.helpers.len(),
            self.env,
        );
        self.helpers.push(body);
        self.helper_ids.insert(key, id);
        id
    }

    fn intern_variant_payload_addressor(
        &mut self,
        variant_ty: Type,
        payload_ty: Type,
        storage: Option<VariantPayloadStorage>,
        static_layout: Option<ResolvedValueLayout>,
    ) -> FunctionId {
        // Storage and static layout are canonical functions of the key's two types. They are
        // passed only to avoid recomputing them while building a newly interned helper.
        let key = PhysicalHelperKey::VariantPayloadAddressor {
            variant_ty,
            payload_ty,
        };
        if let Some(id) = self.helper_ids.get(&key) {
            return *id;
        }
        let id = self.next_helper_id();
        let body = build_variant_payload_addressor(
            variant_ty,
            payload_ty,
            storage,
            static_layout,
            self.helpers.len(),
            self.known,
            self.env,
        );
        self.helpers.push(body);
        self.helper_ids.insert(key, id);
        id
    }

    fn intern_variant_payload_release(&mut self, variant_ty: Type, payload_ty: Type) -> FunctionId {
        let key = PhysicalHelperKey::VariantPayloadRelease {
            variant_ty,
            payload_ty,
        };
        if let Some(id) = self.helper_ids.get(&key) {
            return *id;
        }
        let id = self.next_helper_id();
        let body =
            build_variant_payload_release(variant_ty, payload_ty, self.helpers.len(), self.env);
        self.helpers.push(body);
        self.helper_ids.insert(key, id);
        id
    }

    fn next_helper_id(&self) -> FunctionId {
        FunctionId::new(
            self.helper_base.module,
            LocalFunctionId::from_index(self.helper_base.function.as_index() + self.helpers.len()),
        )
    }

    fn intern_product_addressor(
        &mut self,
        key: ProductAddressorKey,
        spec: &ProductLayoutSpec,
    ) -> FunctionId {
        let helper_key = PhysicalHelperKey::Product(key.clone());
        if let Some(id) = self.helper_ids.get(&helper_key) {
            return *id;
        }
        let id = self.next_helper_id();
        let body = build_product_addressor(&key, spec, self.helpers.len(), self.known, self.env);
        self.helpers.push(body);
        self.helper_ids.insert(helper_key, id);
        id
    }
}

fn buffer_call_type(
    operation: &Operation,
    visible_arguments: usize,
    function: FunctionId,
) -> Result<&CallImplType, BackendReadinessError> {
    let OperationKind::Call { ty, .. } = &operation.kind else {
        return Err(BackendReadinessError::InvalidBufferCall { function });
    };
    if ty.fn_ty.args.len() != visible_arguments || operation.operands.len() != visible_arguments + 2
    {
        return Err(BackendReadinessError::InvalidBufferCall { function });
    }
    Ok(ty)
}

fn buffer_argument_element_type(
    call_ty: &CallImplType,
    argument: usize,
    function: FunctionId,
) -> Result<Type, BackendReadinessError> {
    call_ty
        .fn_ty
        .args
        .get(argument)
        .and_then(|argument| buffer_element_type(argument.ty))
        .ok_or(BackendReadinessError::InvalidBufferCall { function })
}

fn edit_result(
    edit: &mut FunctionEdit,
    operations: &mut Vec<Operation>,
    mut operation: Operation,
) -> Value {
    let result = edit
        .assign_new_result(&mut operation)
        .expect("the inserted operation produces a result");
    operations.push(operation);
    result
}

fn edit_int_constant(edit: &mut FunctionEdit, value: isize, env: ModuleEnv<'_>) -> Value {
    Value::Constant(edit.add_constant(int_type(), LiteralValue::new_native(value), &env))
}

fn edit_int_binary(
    edit: &mut FunctionEdit,
    operations: &mut Vec<Operation>,
    callee: (FunctionId, &CallImplType),
    left: Value,
    right: Value,
    span: Location,
) -> Value {
    let result = edit_result(edit, operations, Operation::alloca(span, int_type()));
    operations.push(Operation::call(
        span,
        Value::Function(callee.0),
        [left, right, result.clone()],
        callee.1.clone(),
    ));
    result
}

fn edit_buffer_pointer_slot(
    edit: &mut FunctionEdit,
    operations: &mut Vec<Operation>,
    buffer: Value,
    element_ty: Type,
    span: Location,
    env: ModuleEnv<'_>,
) -> Value {
    let zero = edit_int_constant(edit, 0, env);
    edit_result(
        edit,
        operations,
        Operation::address_offset_place(span, buffer, zero, element_ty),
    )
}

#[allow(clippy::too_many_arguments)]
fn edit_buffer_element_address(
    edit: &mut FunctionEdit,
    operations: &mut Vec<Operation>,
    buffer: Value,
    index: Value,
    element_size: Value,
    element_ty: Type,
    known: &KnownCallees,
    span: Location,
    env: ModuleEnv<'_>,
) -> Value {
    let pointer_slot = edit_buffer_pointer_slot(edit, operations, buffer, element_ty, span, env);
    let base = edit_result(edit, operations, Operation::load(span, pointer_slot));
    let offset = edit_int_binary(edit, operations, known.int_mul(), index, element_size, span);
    let offset = edit_result(edit, operations, Operation::load(span, offset));
    edit_result(
        edit,
        operations,
        Operation::address_offset(span, base, offset, element_ty, None),
    )
}

fn edit_store_unit(
    edit: &mut FunctionEdit,
    operations: &mut Vec<Operation>,
    destination: Value,
    span: Location,
    env: ModuleEnv<'_>,
) {
    let unit = edit.add_constant(Type::unit(), LiteralValue::new_native(()), &env);
    operations.push(Operation::store(span, Value::Constant(unit), destination));
}

fn build_buffer_drop(
    buffer_ty: Type,
    element_ty: Type,
    helper_index: usize,
    env: ModuleEnv<'_>,
) -> Function {
    let span = Location::new_synthesized();
    let name = Ustr::from(&format!("#physical:buffer_drop:{helper_index}"));
    let mut builder = FunctionBuilder::new(name, CallResultConvention::Value);
    let buffer = Value::Parameter(builder.add_parameter(
        buffer_ty,
        ParameterKind::Parameter(ArgConvention::MutableRef),
    ));
    let destination = Value::Parameter(builder.add_parameter(Type::unit(), ParameterKind::Return));
    let entry = builder.add_block();
    let zero = builder.add_constant(int_type(), LiteralValue::new_native(0isize), &env);
    let pointer_slot = append_result(
        &mut builder,
        entry,
        Operation::address_offset_place(span, buffer, Value::Constant(zero), element_ty),
    );
    let allocation = append_result(
        &mut builder,
        entry,
        Operation::load(span, pointer_slot.clone()),
    );
    builder.append_operation(entry, Operation::runtime_dealloc(span, allocation));
    builder.append_operation(entry, Operation::clear(span, pointer_slot));
    finish_unit_result(&mut builder, entry, destination, span, env);
    builder.finish_unverified()
}

fn variant_payload_projections(
    function: FunctionId,
    body: &Function,
    env: ModuleEnv<'_>,
) -> Result<Vec<VariantPayloadProjection>, BackendReadinessError> {
    let candidates = body
        .blocks()
        .flat_map(|block| {
            body.block(block)
                .operations()
                .iter()
                .enumerate()
                .filter(|(_, operation)| {
                    matches!(
                        operation.kind,
                        OperationKind::Subfield {
                            variant_payload: true,
                            ..
                        }
                    )
                })
                .map(move |(operation_index, operation)| {
                    (block, operation_index, operation.clone())
                })
        })
        .collect::<Vec<_>>();
    if candidates.is_empty() {
        return Ok(Vec::new());
    }

    let roles = ValueRoles::derive(body);
    let mut projections = Vec::new();
    for (block, operation_index, operation) in candidates {
        operation
            .result_id()
            .ok_or(BackendReadinessError::InvalidVariantPayloadProjection { function })?;
        let variant_ty = roles
            .get(&operation.operands[0], body.constants())
            .and_then(|role| role.place_pointee_type())
            .and_then(|ty| match ty {
                MirType::Lowered(ty) => Some(ty),
                MirType::Pointer(_) => None,
            })
            .ok_or(BackendReadinessError::InvalidVariantPayloadProjection { function })?;
        let payload_ty = match operation.kind {
            OperationKind::Subfield { ty, .. } => ty,
            _ => unreachable!(),
        };
        let storage = variant_payload_storage_for_payload_type(variant_ty, payload_ty, &env);
        projections.push(VariantPayloadProjection {
            block,
            operation_index,
            operation,
            variant_ty,
            storage,
        });
    }
    Ok(projections)
}

fn value_drop_variant(
    original: FunctionId,
    body: &FunctionEdit,
    env: ModuleEnv<'_>,
) -> Option<(Value, Type, Type)> {
    // `Value::drop` has exactly one visible argument, `&mut Self`; any other mutable-reference
    // shape is not the trait method whose representation lifetime physical lowering owns.
    let mut mutable_parameters = body
        .parameters()
        .iter()
        .enumerate()
        .filter(|(_, parameter)| {
            matches!(
                parameter.kind,
                ParameterKind::Parameter(ArgConvention::MutableRef)
            )
        });
    let (index, _) = mutable_parameters.next()?;
    if mutable_parameters.next().is_some() {
        return None;
    }
    let parameter = ParameterId::from_index(index);
    let variant_ty = body.parameters()[parameter.as_index()].ty;
    let payload_ty = variant_indirect_payload_type(variant_ty, &env)?;
    if !is_value_drop_function(original, &env) {
        return None;
    }
    Some((Value::Parameter(parameter), variant_ty, payload_ty))
}

fn bool_constant(edit: &mut FunctionEdit, value: bool, env: ModuleEnv<'_>) -> ConstantId {
    edit.add_constant(bool_type(), LiteralValue::new_native(value), &env)
}

fn append_edit_result(edit: &mut FunctionEdit, block: BlockId, mut operation: Operation) -> Value {
    let result = edit
        .assign_new_result(&mut operation)
        .expect("operation produces a result");
    edit.block_mut(block).operations.push(operation);
    result
}

fn variant_payload_addressor_call_type(variant_ty: Type, payload_ty: Type) -> CallImplType {
    CallImplType::new(
        FnType::new_mut_resolved([(variant_ty, true)], payload_ty, no_effects()),
        CallResultConvention::ADDRESSOR_PLACE,
    )
}

fn variant_payload_helper_call_type(variant_ty: Type) -> CallImplType {
    CallImplType::value(FnType::new_mut_resolved(
        [(variant_ty, true)],
        Type::unit(),
        no_effects(),
    ))
}

fn variant_payload_release_call(
    edit: &mut FunctionEdit,
    helper: FunctionId,
    base: Value,
    variant_ty: Type,
    span: Location,
) -> Vec<Operation> {
    let mut result_operation = Operation::alloca(span, Type::unit());
    let result = edit
        .assign_new_result(&mut result_operation)
        .expect("alloca produces a place");
    let call = Operation::call(
        span,
        Value::Function(helper),
        [base, result],
        variant_payload_helper_call_type(variant_ty),
    );
    vec![result_operation, call]
}

fn build_variant_payload_allocation(
    variant_ty: Type,
    payload_ty: Type,
    storage: Option<VariantPayloadStorage>,
    static_layout: Option<ResolvedValueLayout>,
    helper_index: usize,
    env: ModuleEnv<'_>,
) -> Function {
    debug_assert_ne!(storage, Some(VariantPayloadStorage::Inline));
    let span = Location::new_synthesized();
    let name = Ustr::from(&format!(
        "#physical:variant_payload_allocation:{helper_index}"
    ));
    let mut builder = FunctionBuilder::new(name, CallResultConvention::Value);
    let witness = static_layout.is_none().then(|| {
        let value_trait = env.expect_std_trait_id(VALUE_TRAIT_NAME);
        let requirement =
            DictionaryReq::new_trait_impl(value_trait, vec![payload_ty], vec![], vec![]);
        Value::Parameter(builder.add_parameter(
            requirement.to_dict_type_in_env(&env),
            ParameterKind::Dictionary,
        ))
    });
    let base = Value::Parameter(builder.add_parameter(
        variant_ty,
        ParameterKind::Parameter(ArgConvention::MutableRef),
    ));
    let destination = Value::Parameter(builder.add_parameter(Type::unit(), ParameterKind::Return));
    let entry = builder.add_block();
    let done = builder.add_block();
    let allocate = if storage == Some(VariantPayloadStorage::Indirect) {
        entry
    } else {
        let allocate = builder.add_block();
        let indirection = append_result(
            &mut builder,
            entry,
            Operation::extract_payload_indirection(span, base.clone()),
        );
        builder.set_terminator(
            entry,
            Terminator::cond_br(span, indirection, allocate, done),
        );
        allocate
    };
    let size = payload_layout_place(
        &mut builder,
        allocate,
        static_layout,
        witness.as_ref(),
        VALUE_SIZE_ASSOC_CONST_INDEX,
        span,
        env,
    );
    let align = payload_layout_place(
        &mut builder,
        allocate,
        static_layout,
        witness.as_ref(),
        VALUE_ALIGN_ASSOC_CONST_INDEX,
        span,
        env,
    );
    let size = append_result(&mut builder, allocate, Operation::load(span, size));
    let align = append_result(&mut builder, allocate, Operation::load(span, align));
    let allocation = append_result(
        &mut builder,
        allocate,
        Operation::runtime_alloc(span, payload_ty, size, align),
    );
    let pointer_layout = ResolvedValueLayout::native::<usize>();
    let slot_offset = isize::try_from(variant_payload_offset(pointer_layout.align)).unwrap();
    let slot_offset = int_constant_value(&mut builder, allocate, slot_offset, span, env);
    let slot = append_result(
        &mut builder,
        allocate,
        Operation::address_offset_place(span, base, slot_offset, payload_ty),
    );
    builder.append_operation(allocate, Operation::store(span, allocation, slot));
    builder.set_terminator(allocate, Terminator::goto(span, done));
    finish_unit_result(&mut builder, done, destination, span, env);
    builder.finish_unverified()
}

#[allow(clippy::too_many_arguments)]
fn build_variant_payload_addressor(
    variant_ty: Type,
    payload_ty: Type,
    storage: Option<VariantPayloadStorage>,
    static_layout: Option<ResolvedValueLayout>,
    helper_index: usize,
    known: &KnownCallees,
    env: ModuleEnv<'_>,
) -> Function {
    let span = Location::new_synthesized();
    let name = Ustr::from(&format!(
        "#physical:variant_payload_addressor:{helper_index}"
    ));
    let mut builder = FunctionBuilder::new(name, CallResultConvention::ADDRESSOR_PLACE);
    let witness = static_layout.is_none().then(|| {
        let value_trait = env.expect_std_trait_id(VALUE_TRAIT_NAME);
        let requirement =
            DictionaryReq::new_trait_impl(value_trait, vec![payload_ty], vec![], vec![]);
        Value::Parameter(builder.add_parameter(
            requirement.to_dict_type_in_env(&env),
            ParameterKind::Dictionary,
        ))
    });
    let base = Value::Parameter(builder.add_parameter(
        variant_ty,
        ParameterKind::Parameter(ArgConvention::MutableRef),
    ));
    let destination = Value::Parameter(builder.add_parameter(payload_ty, ParameterKind::Return));
    let entry = builder.add_block();
    let (inline, indirect) = match storage {
        Some(VariantPayloadStorage::Inline) => (Some(entry), None),
        Some(VariantPayloadStorage::Indirect) => (None, Some(entry)),
        None => {
            let inline = builder.add_block();
            let indirect = builder.add_block();
            let indirection = append_result(
                &mut builder,
                entry,
                Operation::extract_payload_indirection(span, base.clone()),
            );
            builder.set_terminator(
                entry,
                Terminator::cond_br(span, indirection, indirect, inline),
            );
            (Some(inline), Some(indirect))
        }
    };

    if let Some(inline) = inline {
        let inline_offset = variant_payload_offset_place(
            &mut builder,
            inline,
            static_layout,
            witness.as_ref(),
            known,
            span,
            env,
        );
        let inline_offset =
            append_result(&mut builder, inline, Operation::load(span, inline_offset));
        let inline_address = append_result(
            &mut builder,
            inline,
            Operation::address_offset(span, base.clone(), inline_offset, payload_ty, None),
        );
        builder.append_operation(
            inline,
            Operation::store(span, inline_address, destination.clone()),
        );
        builder.set_terminator(inline, Terminator::ret(span));
    }

    if let Some(indirect) = indirect {
        let pointer_layout = ResolvedValueLayout::native::<usize>();
        let slot_offset = isize::try_from(variant_payload_offset(pointer_layout.align)).unwrap();
        let slot_offset = int_constant_value(&mut builder, indirect, slot_offset, span, env);
        let slot = append_result(
            &mut builder,
            indirect,
            Operation::address_offset_place(span, base, slot_offset, payload_ty),
        );
        let address = append_result(&mut builder, indirect, Operation::load(span, slot));
        builder.append_operation(indirect, Operation::store(span, address, destination));
        builder.set_terminator(indirect, Terminator::ret(span));
    }
    builder.finish_unverified()
}

fn finish_unit_result(
    builder: &mut FunctionBuilder,
    block: BlockId,
    destination: Value,
    span: Location,
    env: ModuleEnv<'_>,
) {
    let unit = builder.add_constant(Type::unit(), LiteralValue::new_native(()), &env);
    builder.append_operation(
        block,
        Operation::store(span, Value::Constant(unit), destination),
    );
    builder.set_terminator(block, Terminator::ret(span));
}

fn build_variant_payload_release(
    variant_ty: Type,
    payload_ty: Type,
    helper_index: usize,
    env: ModuleEnv<'_>,
) -> Function {
    let span = Location::new_synthesized();
    let name = Ustr::from(&format!("#physical:variant_payload_release:{helper_index}"));
    let mut builder = FunctionBuilder::new(name, CallResultConvention::Value);
    let base = Value::Parameter(builder.add_parameter(
        variant_ty,
        ParameterKind::Parameter(ArgConvention::MutableRef),
    ));
    let destination = Value::Parameter(builder.add_parameter(Type::unit(), ParameterKind::Return));
    let entry = builder.add_block();
    let done = builder.add_block();
    let storage_check = builder.add_block();
    let base_initialized = append_result(
        &mut builder,
        entry,
        Operation::is_initialized(span, base.clone()),
    );
    builder.set_terminator(
        entry,
        Terminator::cond_br(span, base_initialized, storage_check, done),
    );
    // A whole variant can mix inline and indirect cases. Release therefore reads the active tag's
    // representation bit rather than specializing on the one pointee type used to type its slot.
    let indirect_check = builder.add_block();
    let indirection = append_result(
        &mut builder,
        storage_check,
        Operation::extract_payload_indirection(span, base.clone()),
    );
    builder.set_terminator(
        storage_check,
        Terminator::cond_br(span, indirection, indirect_check, done),
    );

    let pointer_layout = ResolvedValueLayout::native::<usize>();
    let offset = isize::try_from(variant_payload_offset(pointer_layout.align)).unwrap();
    let offset = int_constant_value(&mut builder, indirect_check, offset, span, env);
    let slot = append_result(
        &mut builder,
        indirect_check,
        Operation::address_offset_place(span, base, offset, payload_ty),
    );
    let release = builder.add_block();
    let slot_initialized = append_result(
        &mut builder,
        indirect_check,
        Operation::is_initialized(span, slot.clone()),
    );
    builder.set_terminator(
        indirect_check,
        Terminator::cond_br(span, slot_initialized, release, done),
    );
    let address = append_result(&mut builder, release, Operation::load(span, slot.clone()));
    builder.append_operation(release, Operation::runtime_dealloc(span, address));
    builder.append_operation(release, Operation::clear(span, slot));
    builder.set_terminator(release, Terminator::goto(span, done));

    let unit = builder.add_constant(Type::unit(), LiteralValue::new_native(()), &env);
    builder.append_operation(
        done,
        Operation::store(span, Value::Constant(unit), destination),
    );
    builder.set_terminator(done, Terminator::ret(span));
    builder.finish_unverified()
}

fn variant_payload_offset_place(
    builder: &mut FunctionBuilder,
    block: BlockId,
    static_layout: Option<ResolvedValueLayout>,
    witness: Option<&Value>,
    known: &KnownCallees,
    span: Location,
    env: ModuleEnv<'_>,
) -> Value {
    if let Some(layout) = static_layout {
        return int_constant_place(
            builder,
            block,
            isize::try_from(variant_payload_offset(layout.align)).unwrap(),
            span,
            env,
        );
    }
    let tag_size = int_constant_place(
        builder,
        block,
        isize::try_from(variant_tag_layout().size).unwrap(),
        span,
        env,
    );
    let align = payload_layout_place(
        builder,
        block,
        None,
        witness,
        VALUE_ALIGN_ASSOC_CONST_INDEX,
        span,
        env,
    );
    align_up_place(builder, block, tag_size, align, known, span, env)
}

fn payload_layout_place(
    builder: &mut FunctionBuilder,
    block: BlockId,
    static_layout: Option<ResolvedValueLayout>,
    witness: Option<&Value>,
    associated_const: TraitAssociatedConstIndex,
    span: Location,
    env: ModuleEnv<'_>,
) -> Value {
    if let Some(layout) = static_layout {
        let value = if associated_const == VALUE_SIZE_ASSOC_CONST_INDEX {
            layout.size
        } else {
            debug_assert_eq!(associated_const, VALUE_ALIGN_ASSOC_CONST_INDEX);
            layout.align
        };
        return int_constant_place(builder, block, isize::try_from(value).unwrap(), span, env);
    }
    value_layout_place(
        builder,
        block,
        witness
            .expect("an open payload has Value layout evidence")
            .clone(),
        associated_const,
        span,
        env,
    )
}

fn int_constant_value(
    builder: &mut FunctionBuilder,
    block: BlockId,
    value: isize,
    span: Location,
    env: ModuleEnv<'_>,
) -> Value {
    let place = int_constant_place(builder, block, value, span, env);
    append_result(builder, block, Operation::load(span, place))
}

fn constant_index(value: &Value, edit: &FunctionEdit) -> Option<ProjectionIndex> {
    let Value::Constant(id) = value else {
        return None;
    };
    edit.constant(*id)
        .representation
        .as_primitive_ty::<isize>()
        .and_then(|index| usize::try_from(*index).ok())
        .and_then(|index| ProjectionIndex::try_from(index).ok())
}

fn product_addressor_call_type(aggregate_ty: Type, field_ty: Type) -> CallImplType {
    CallImplType::new(
        FnType::new_mut_resolved([(aggregate_ty, true)], field_ty, no_effects()),
        CallResultConvention::ADDRESSOR_PLACE,
    )
}

fn build_product_addressor(
    key: &ProductAddressorKey,
    spec: &ProductLayoutSpec,
    helper_index: usize,
    known: &KnownCallees,
    env: ModuleEnv<'_>,
) -> Function {
    let span = Location::new_synthesized();
    let name = Ustr::from(&format!("#physical:product_addressor:{helper_index}"));
    let mut builder = FunctionBuilder::new(name, CallResultConvention::ADDRESSOR_PLACE);
    let value_trait = env.expect_std_trait_id(VALUE_TRAIT_NAME);
    let member_witnesses = spec
        .members
        .iter()
        .map(|member| {
            member.static_layout.is_none().then(|| {
                let requirement =
                    DictionaryReq::new_trait_impl(value_trait, vec![member.ty], vec![], vec![]);
                Value::Parameter(builder.add_parameter(
                    requirement.to_dict_type_in_env(&env),
                    ParameterKind::Dictionary,
                ))
            })
        })
        .collect::<Vec<_>>();
    let base = Value::Parameter(builder.add_parameter(
        key.aggregate_ty,
        ParameterKind::Parameter(ArgConvention::MutableRef),
    ));
    let field = spec.members[key.field_index.as_index()];
    let destination = Value::Parameter(builder.add_parameter(field.ty, ParameterKind::Return));
    let entry = builder.add_block();

    match spec.order {
        ProductLayoutOrder::Positional => build_positional_product_addressor(
            builder,
            entry,
            key,
            spec,
            &member_witnesses,
            base,
            destination,
            known,
            span,
            env,
        ),
        ProductLayoutOrder::CompactRecord => build_compact_record_addressor(
            builder,
            entry,
            key,
            spec,
            &member_witnesses,
            base,
            destination,
            known,
            span,
            env,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn build_positional_product_addressor(
    mut builder: FunctionBuilder,
    block: BlockId,
    key: &ProductAddressorKey,
    spec: &ProductLayoutSpec,
    member_witnesses: &[Option<Value>],
    base: Value,
    destination: Value,
    known: &KnownCallees,
    span: Location,
    env: ModuleEnv<'_>,
) -> Function {
    let mut offset = int_constant_place(&mut builder, block, 0, span, env);
    for (index, member) in spec.members.iter().enumerate() {
        let align = member_layout_place(
            &mut builder,
            block,
            *member,
            member_witnesses[index].as_ref(),
            VALUE_ALIGN_ASSOC_CONST_INDEX,
            span,
            env,
        );
        offset = align_up_place(&mut builder, block, offset, align, known, span, env);
        if index == key.field_index.as_index() {
            return finish_product_addressor(
                builder,
                block,
                *member,
                base,
                destination,
                offset,
                key.field_index,
                span,
            );
        }
        let size = member_layout_place(
            &mut builder,
            block,
            *member,
            member_witnesses[index].as_ref(),
            VALUE_SIZE_ASSOC_CONST_INDEX,
            span,
            env,
        );
        offset = int_binary(&mut builder, block, known.int_add(), offset, size, span);
    }
    unreachable!("the product addressor field was validated against the layout recipe")
}

#[allow(clippy::too_many_arguments)]
fn build_compact_record_addressor(
    mut builder: FunctionBuilder,
    mut block: BlockId,
    key: &ProductAddressorKey,
    spec: &ProductLayoutSpec,
    member_witnesses: &[Option<Value>],
    base: Value,
    destination: Value,
    known: &KnownCallees,
    span: Location,
    env: ModuleEnv<'_>,
) -> Function {
    let target = key.field_index.as_index();
    let target_static_layout = spec.members[target].static_layout;
    let mut static_offset = 0isize;
    if let Some(target_layout) = target_static_layout {
        for (candidate, member) in spec.members.iter().enumerate() {
            if candidate == target {
                continue;
            }
            let Some(candidate_layout) = member.static_layout else {
                continue;
            };
            if spec.compact_member_precedes(
                ProjectionIndex::from_index(candidate),
                key.field_index,
                candidate_layout.align.cmp(&target_layout.align),
            ) {
                static_offset = static_offset
                    .checked_add(
                        candidate_layout
                            .size
                            .try_into()
                            .expect("Value size fits in int"),
                    )
                    .expect("product offset fits in int");
            }
        }
    }
    let offset = int_constant_place(&mut builder, block, static_offset, span, env);
    let target_align = member_layout_place(
        &mut builder,
        block,
        spec.members[target],
        member_witnesses[target].as_ref(),
        VALUE_ALIGN_ASSOC_CONST_INDEX,
        span,
        env,
    );
    // Compact order is decreasing alignment. Every preceding member's power-of-two alignment is
    // therefore a multiple of the target alignment, and its size is a multiple of that alignment;
    // summing preceding sizes already produces an aligned target offset without padding.
    for (candidate, member) in spec.members.iter().enumerate() {
        if candidate == target {
            continue;
        }
        let candidate_index = ProjectionIndex::from_index(candidate);
        if member.static_layout.is_some() && target_static_layout.is_some() {
            continue;
        }
        let candidate_align = member_layout_place(
            &mut builder,
            block,
            *member,
            member_witnesses[candidate].as_ref(),
            VALUE_ALIGN_ASSOC_CONST_INDEX,
            span,
            env,
        );
        let add = builder.add_block();
        let next = builder.add_block();
        let ordering = binary_call(
            &mut builder,
            block,
            known.int_cmp(),
            candidate_align,
            target_align.clone(),
            span,
        );
        let tag = append_result(&mut builder, block, Operation::extract_tag(span, ordering));
        let mut cases = vec![(Ustr::from(ORDERING_GREATER), add)];
        if spec.compact_member_precedes(candidate_index, key.field_index, Ordering::Equal) {
            cases.push((Ustr::from(ORDERING_EQUAL), add));
        }
        builder.set_terminator(block, Terminator::switch_variant(span, tag, cases, next));

        add_member_size_to_offset(
            &mut builder,
            add,
            *member,
            member_witnesses[candidate].as_ref(),
            &offset,
            known,
            span,
            env,
        );
        builder.set_terminator(add, Terminator::goto(span, next));
        block = next;
    }
    finish_product_addressor(
        builder,
        block,
        spec.members[target],
        base,
        destination,
        offset,
        key.field_index,
        span,
    )
}

#[allow(clippy::too_many_arguments)]
fn finish_product_addressor(
    mut builder: FunctionBuilder,
    block: BlockId,
    member: ProductMemberLayout,
    base: Value,
    destination: Value,
    offset: Value,
    field_index: ProjectionIndex,
    span: Location,
) -> Function {
    let byte_offset = append_result(&mut builder, block, Operation::load(span, offset));
    let projection =
        Operation::address_offset(span, base, byte_offset, member.ty, Some(field_index));
    let address = append_result(&mut builder, block, projection);
    builder.append_operation(block, Operation::store(span, address, destination));
    builder.set_terminator(block, Terminator::ret(span));
    builder.finish_unverified()
}

fn append_result(builder: &mut FunctionBuilder, block: BlockId, operation: Operation) -> Value {
    builder
        .append_operation(block, operation)
        .expect("the generated operation produces a result")
}

fn int_constant_place(
    builder: &mut FunctionBuilder,
    block: BlockId,
    value: isize,
    span: Location,
    env: ModuleEnv<'_>,
) -> Value {
    let constant = builder.add_constant(int_type(), LiteralValue::new_native(value), &env);
    let place = append_result(builder, block, Operation::alloca(span, int_type()));
    builder.append_operation(
        block,
        Operation::store(span, Value::Constant(constant), place.clone()),
    );
    place
}

fn value_layout_place(
    builder: &mut FunctionBuilder,
    block: BlockId,
    dictionary: Value,
    associated_const: TraitAssociatedConstIndex,
    span: Location,
    env: ModuleEnv<'_>,
) -> Value {
    let (entry, getter_ty) = value_layout_getter_entry(&env, associated_const);
    let getter = append_result(
        builder,
        block,
        Operation::dict_entry(
            span,
            dictionary,
            entry,
            Type::function_type(getter_ty.clone()),
        ),
    );
    let result = append_result(builder, block, Operation::alloca(span, int_type()));
    builder.append_operation(
        block,
        Operation::call(
            span,
            getter,
            [result.clone()],
            CallImplType::value(getter_ty),
        ),
    );
    result
}

fn member_layout_place(
    builder: &mut FunctionBuilder,
    block: BlockId,
    member: ProductMemberLayout,
    witness: Option<&Value>,
    associated_const: TraitAssociatedConstIndex,
    span: Location,
    env: ModuleEnv<'_>,
) -> Value {
    if let Some(layout) = member.static_layout {
        let value = if associated_const == VALUE_SIZE_ASSOC_CONST_INDEX {
            layout.size
        } else {
            debug_assert_eq!(associated_const, VALUE_ALIGN_ASSOC_CONST_INDEX);
            layout.align
        };
        return int_constant_place(
            builder,
            block,
            value.try_into().expect("Value layout fits in int"),
            span,
            env,
        );
    }
    value_layout_place(
        builder,
        block,
        witness
            .expect("an open member has Value layout evidence")
            .clone(),
        associated_const,
        span,
        env,
    )
}

#[allow(clippy::too_many_arguments)]
fn add_member_size_to_offset(
    builder: &mut FunctionBuilder,
    block: BlockId,
    member: ProductMemberLayout,
    witness: Option<&Value>,
    offset: &Value,
    known: &KnownCallees,
    span: Location,
    env: ModuleEnv<'_>,
) {
    let size = member_layout_place(
        builder,
        block,
        member,
        witness,
        VALUE_SIZE_ASSOC_CONST_INDEX,
        span,
        env,
    );
    let sum = int_binary(builder, block, known.int_add(), offset.clone(), size, span);
    let sum = append_result(builder, block, Operation::load(span, sum));
    builder.append_operation(block, Operation::store(span, sum, offset.clone()));
}

fn align_up_place(
    builder: &mut FunctionBuilder,
    block: BlockId,
    offset: Value,
    align: Value,
    known: &KnownCallees,
    span: Location,
    env: ModuleEnv<'_>,
) -> Value {
    let one = int_constant_place(builder, block, 1, span, env);
    let align_minus_one = int_binary(builder, block, known.int_sub(), align.clone(), one, span);
    let upper = int_binary(
        builder,
        block,
        known.int_add(),
        offset,
        align_minus_one,
        span,
    );
    let negated_align = int_unary(builder, block, known.int_neg(), align, span);
    int_binary(
        builder,
        block,
        known.int_bit_and(),
        upper,
        negated_align,
        span,
    )
}

fn int_binary(
    builder: &mut FunctionBuilder,
    block: BlockId,
    callee: (FunctionId, &CallImplType),
    left: Value,
    right: Value,
    span: Location,
) -> Value {
    debug_assert_eq!(callee.1.ret(), int_type());
    binary_call(builder, block, callee, left, right, span)
}

fn binary_call(
    builder: &mut FunctionBuilder,
    block: BlockId,
    callee: (FunctionId, &CallImplType),
    left: Value,
    right: Value,
    span: Location,
) -> Value {
    let result = append_result(builder, block, Operation::alloca(span, callee.1.ret()));
    builder.append_operation(
        block,
        Operation::call(
            span,
            Value::Function(callee.0),
            [left, right, result.clone()],
            callee.1.clone(),
        ),
    );
    result
}

fn int_unary(
    builder: &mut FunctionBuilder,
    block: BlockId,
    callee: (FunctionId, &CallImplType),
    value: Value,
    span: Location,
) -> Value {
    let result = append_result(builder, block, Operation::alloca(span, int_type()));
    builder.append_operation(
        block,
        Operation::call(
            span,
            Value::Function(callee.0),
            [value, result.clone()],
            callee.1.clone(),
        ),
    );
    result
}

/// The shared call boundary has exactly one trailing result parameter, even for scoped accessors.
/// A Project supplies its result through the yield protocol rather than an explicit out-pointer.
fn physical_call_arity(body: &Function, projection: bool) -> Option<usize> {
    let (result, inputs) = body.parameters().split_last()?;
    if result.kind != ParameterKind::Return
        || inputs
            .iter()
            .any(|parameter| parameter.kind == ParameterKind::Return)
    {
        return None;
    }
    Some(inputs.len() + usize::from(!projection))
}

fn verify_physical_mir(
    artifacts: &BackendReadyMirArtifacts,
    env: ModuleEnv<'_>,
) -> Result<(), BackendReadinessError> {
    verify_dictionary_catalog(artifacts)?;
    verify_subscript_catalog(artifacts)?;
    let module = artifacts.module;
    for index in 0..artifacts.entry_count() {
        let function = LocalFunctionId::from_index(index);
        let Some(body) = artifacts.get(function) else {
            continue;
        };
        let function_id = FunctionId::new(module, function);
        let constructed_dictionaries = constructed_dictionary_definitions(body);
        let constructed_subscripts = constructed_subscript_definitions(body);

        for block in body.blocks() {
            let block = body.block(block);
            for operation in block.operations() {
                verify_physical_operation(
                    artifacts,
                    function_id,
                    &constructed_dictionaries,
                    &constructed_subscripts,
                    operation,
                )?;
            }
            // Exhaustive just like operation classification: new terminators require an explicit
            // physical contract. Existing failure flow and scoped yields remain physical MIR.
            match &block.terminator().kind {
                TerminatorKind::Invoke { operation, .. } => {
                    verify_physical_operation(
                        artifacts,
                        function_id,
                        &constructed_dictionaries,
                        &constructed_subscripts,
                        operation,
                    )?;
                    continue;
                }
                TerminatorKind::Yield { .. } => {
                    if !body.result_convention().requires_yield_driver() {
                        return Err(BackendReadinessError::InvalidPhysicalProtocol {
                            function: function_id,
                            reason: "yield requires a scoped accessor entry",
                        });
                    }
                }
                TerminatorKind::Goto { .. }
                | TerminatorKind::CondBr { .. }
                | TerminatorKind::SwitchVariant { .. }
                | TerminatorKind::Return
                | TerminatorKind::PropagateError
                | TerminatorKind::FailureDuringCleanup
                | TerminatorKind::InvariantFailure { .. } => {}
            }
            verify_local_function_operands(
                module,
                artifacts.entry_count(),
                function_id,
                block.terminator().operands().iter(),
            )?;
            verify_evidence_operands(artifacts, function_id, block.terminator().operands().iter())?;
        }
        if physical_call_arity(body, false).is_none() {
            return Err(BackendReadinessError::InvalidPhysicalProtocol {
                function: function_id,
                reason: "entry requires exactly one trailing result parameter",
            });
        }
        // Compiler-generated malformed MIR is an invariant failure, diagnosed by the shared
        // verifier's assertions in every build. Unsupported physical contracts return errors.
        verify_physical_function(body, env);
    }
    Ok(())
}

fn verify_physical_operation(
    artifacts: &BackendReadyMirArtifacts,
    owner: FunctionId,
    constructed_dictionaries: &FxHashMap<ValueId, TraitDictionaryId>,
    constructed_subscripts: &FxHashMap<ValueId, ConstructedSubscript>,
    operation: &Operation,
) -> Result<(), BackendReadinessError> {
    // Deliberately exhaustive: every new MIR operation needs a physical execution contract.
    // Acceptance here describes the IR, not the operation subset of an individual executor.
    let unresolved = match &operation.kind {
        OperationKind::Subfield {
            variant_payload: true,
            ..
        } => Some("variant_payload"),
        OperationKind::Subfield {
            variant_payload: false,
            ..
        } => Some("subfield"),
        OperationKind::SubscriptMember { .. } => Some("subscript_member"),
        OperationKind::Alloca { .. }
        | OperationKind::AllocaPlace { .. }
        | OperationKind::RuntimeAlloc { .. }
        | OperationKind::RuntimeDealloc
        | OperationKind::Call { .. }
        | OperationKind::Project { .. }
        | OperationKind::EndProject
        | OperationKind::CompareEqual
        | OperationKind::Load
        | OperationKind::AddressOffset { .. }
        | OperationKind::AddressOffsetPlace { .. }
        | OperationKind::DictEntry { .. }
        | OperationKind::BuildDictionary { .. }
        | OperationKind::BuildSubscriptEvidence { .. }
        | OperationKind::BuildSubscript { .. }
        | OperationKind::CloneSubscriptEnv { .. }
        | OperationKind::DropSubscriptEnv
        | OperationKind::BorrowSubscriptMember { .. }
        | OperationKind::Variant { .. }
        | OperationKind::BuildArray { .. }
        | OperationKind::ExtractTag
        | OperationKind::ExtractPayloadIndirection
        | OperationKind::IsInitialized
        | OperationKind::Store
        | OperationKind::Clear
        | OperationKind::Memcpy
        | OperationKind::Move
        | OperationKind::Replace
        | OperationKind::MoveBytes { .. }
        | OperationKind::StackSave
        | OperationKind::StackRestore
        | OperationKind::CheckCallDepth
        | OperationKind::CheckFuel
        | OperationKind::Clone { .. }
        | OperationKind::Drop { .. }
        | OperationKind::BuildClosure { .. }
        | OperationKind::CloneClosureEnv { .. }
        | OperationKind::DropClosureEnv => None,
    };
    if let Some(operation) = unresolved {
        return Err(BackendReadinessError::UnresolvedPhysicalOperation {
            function: owner,
            operation,
        });
    }
    if matches!(&operation.kind, OperationKind::Call { ty, .. } if ty.result_convention.requires_yield_driver())
    {
        return Err(BackendReadinessError::InvalidPhysicalProtocol {
            function: owner,
            reason: "scoped accessor requires project, not call",
        });
    }
    verify_local_function_operands(
        artifacts.module,
        artifacts.entry_count(),
        owner,
        operation.operands.iter(),
    )?;
    verify_evidence_operation(
        artifacts,
        owner,
        constructed_dictionaries,
        constructed_subscripts,
        operation,
    )?;
    if let Some(target) = operation.kind.function_id() {
        verify_local_function_target(artifacts.module, artifacts.entry_count(), owner, target)?;
    }
    verify_direct_call(artifacts, owner, operation)
}

fn constructed_dictionary_definitions(body: &Function) -> FxHashMap<ValueId, TraitDictionaryId> {
    let mut definitions = FxHashMap::default();
    for block in body.blocks() {
        let block = body.block(block);
        for operation in block.operations() {
            record_constructed_dictionary(operation, &mut definitions);
        }
        if let TerminatorKind::Invoke { operation, .. } = &block.terminator().kind {
            record_constructed_dictionary(operation, &mut definitions);
        }
    }
    definitions
}

fn record_constructed_dictionary(
    operation: &Operation,
    definitions: &mut FxHashMap<ValueId, TraitDictionaryId>,
) {
    if let OperationKind::BuildDictionary { definition, .. } = operation.kind {
        let result = operation
            .result_id()
            .expect("build_dictionary produces a dictionary value");
        assert!(definitions.insert(result, definition).is_none());
    }
}

#[derive(Clone, Copy)]
struct ConstructedSubscript {
    definition: SubscriptId,
    capture_count: usize,
}

fn constructed_subscript_definitions(body: &Function) -> FxHashMap<ValueId, ConstructedSubscript> {
    let operations = body
        .blocks()
        .flat_map(|block| {
            let block = body.block(block);
            block
                .operations()
                .iter()
                .chain(match &block.terminator().kind {
                    TerminatorKind::Invoke { operation, .. } => from_ref(operation),
                    _ => &[],
                })
        })
        .filter(|operation| matches!(operation.kind, OperationKind::BuildSubscriptEvidence { .. }))
        .collect::<Vec<_>>();
    let mut results = FxHashSet::default();
    for operation in &operations {
        let result = operation
            .result_id()
            .expect("build_subscript_evidence produces subscript evidence");
        assert!(results.insert(result), "MIR values have unique definitions");
    }
    let mut definitions = FxHashMap::default();
    loop {
        let mut changed = false;
        for operation in &operations {
            let result = operation
                .result_id()
                .expect("build_subscript_evidence produces subscript evidence");
            if definitions.contains_key(&result) {
                continue;
            }
            let Some(base) = operation
                .operands
                .first()
                .and_then(|base| static_subscript(base, &definitions))
            else {
                continue;
            };
            definitions.insert(
                result,
                ConstructedSubscript {
                    definition: base.definition,
                    capture_count: base.capture_count + operation.operands.len() - 1,
                },
            );
            changed = true;
        }
        if !changed {
            return definitions;
        }
    }
}

fn verify_dictionary_catalog(
    artifacts: &BackendReadyMirArtifacts,
) -> Result<(), BackendReadinessError> {
    for (index, definition) in artifacts.dictionaries().iter().enumerate() {
        let expected_id = TraitDictionaryId::new(artifacts.module, LocalImplId::from_index(index));
        if definition.id() != expected_id {
            return Err(BackendReadinessError::InvalidDictionaryDefinition {
                dictionary: definition.id(),
            });
        }
        for entry in definition.entries() {
            let target = entry.function();
            if artifacts.native_signature(target).is_some() && !entry.capture_mapping().is_empty() {
                return Err(BackendReadinessError::InvalidDictionaryEntry {
                    dictionary: definition.id(),
                    target,
                });
            }
            // Native entries legitimately occupy a function-table slot without a MIR body.
            if target.module != artifacts.module
                || target.function.as_index() >= artifacts.entry_count()
            {
                return Err(BackendReadinessError::InvalidDictionaryEntry {
                    dictionary: definition.id(),
                    target,
                });
            }
            if entry.capture_mapping().iter().any(|mapping| {
                matches!(mapping, DictionaryEntryEvidence::Capture(capture) if *capture >= definition.capture_schema().len())
            }) {
                return Err(BackendReadinessError::InvalidDictionaryDefinition {
                    dictionary: definition.id(),
                });
            }
        }
    }
    Ok(())
}

fn verify_subscript_catalog(
    artifacts: &BackendReadyMirArtifacts,
) -> Result<(), BackendReadinessError> {
    for (index, definition) in artifacts.subscripts().iter().enumerate() {
        let expected_id = SubscriptId::new(artifacts.module, LocalSubscriptId::from_index(index));
        if definition.id() != expected_id {
            return Err(BackendReadinessError::InvalidSubscriptDefinition {
                subscript: definition.id(),
            });
        }
        for mut_member in [false, true] {
            let Some(member) = definition.member(mut_member) else {
                continue;
            };
            let target = member.function();
            if let Some(NativeResult::Addressor { mutable, .. }) = artifacts
                .native_signature(target)
                .map(|signature| signature.result)
                && mutable != mut_member
            {
                return Err(BackendReadinessError::InvalidSubscriptMember {
                    subscript: definition.id(),
                    target,
                });
            }
            // Native members legitimately occupy a function-table slot without a MIR body.
            if target.module != artifacts.module
                || target.function.as_index() >= artifacts.entry_count()
            {
                return Err(BackendReadinessError::InvalidSubscriptMember {
                    subscript: definition.id(),
                    target,
                });
            }
        }
    }
    Ok(())
}

fn verify_evidence_operation(
    artifacts: &BackendReadyMirArtifacts,
    owner: FunctionId,
    constructed_dictionaries: &FxHashMap<ValueId, TraitDictionaryId>,
    constructed_subscripts: &FxHashMap<ValueId, ConstructedSubscript>,
    operation: &Operation,
) -> Result<(), BackendReadinessError> {
    if matches!(operation.kind, OperationKind::BuildSubscriptEvidence { .. }) {
        let base = operation
            .operands
            .first()
            .expect("build_subscript_evidence has a base operand");
        verify_subscript_base(artifacts, owner, base)?;
        verify_evidence_operands(artifacts, owner, operation.operands[1..].iter())?;
    } else {
        verify_evidence_operands(artifacts, owner, operation.operands.iter())?;
    }

    if let OperationKind::BuildDictionary { definition, .. } = operation.kind {
        verify_dictionary_reference(artifacts, owner, definition)?;
        if let Some(metadata) = artifacts.dictionary(definition)
            && operation.operands.len() != metadata.capture_schema().len()
        {
            return Err(BackendReadinessError::InvalidDictionaryCaptureCount {
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
            .and_then(|value| static_dictionary_definition(value, constructed_dictionaries))
        && artifacts.dictionary(definition).is_some()
        && artifacts
            .dictionary_entry(definition, entry_index)
            .is_none()
    {
        return Err(BackendReadinessError::InvalidDictionaryEntryIndex {
            owner,
            dictionary: definition,
            entry: entry_index,
        });
    }

    if matches!(operation.kind, OperationKind::BuildSubscriptEvidence { .. }) {
        let result = operation
            .result_id()
            .expect("build_subscript_evidence produces subscript evidence");
        if let Some(value) = constructed_subscripts.get(&result)
            && let Some(definition) = artifacts.subscript(value.definition)
            && value.capture_count != definition.capture_schema().len()
        {
            return Err(BackendReadinessError::InvalidSubscriptCaptureCount {
                owner,
                subscript: value.definition,
                expected: definition.capture_schema().len(),
                actual: value.capture_count,
            });
        }
    }
    if let OperationKind::BorrowSubscriptMember { mut_member, .. } = operation.kind
        && let Some(value) = operation
            .operands
            .first()
            .and_then(|operand| static_subscript(operand, constructed_subscripts))
        && let Some(definition) = artifacts.subscript(value.definition)
        && definition.member(mut_member).is_none()
    {
        return Err(BackendReadinessError::MissingSubscriptMember {
            owner,
            subscript: value.definition,
            mut_member,
        });
    }
    Ok(())
}

fn verify_subscript_base(
    artifacts: &BackendReadyMirArtifacts,
    owner: FunctionId,
    value: &Value,
) -> Result<(), BackendReadinessError> {
    match value {
        Value::Subscript(definition) => verify_subscript_reference(artifacts, owner, *definition),
        Value::Evidence(evidence) => match evidence.as_ref() {
            StaticEvidence::Subscript {
                definition,
                captures,
            } => {
                verify_subscript_reference(artifacts, owner, *definition)?;
                for capture in captures {
                    verify_static_evidence(artifacts, owner, capture)?;
                }
                Ok(())
            }
            _ => verify_static_evidence(artifacts, owner, evidence),
        },
        _ => verify_evidence_value(artifacts, owner, value),
    }
}

fn verify_evidence_operands<'a>(
    artifacts: &BackendReadyMirArtifacts,
    owner: FunctionId,
    operands: impl Iterator<Item = &'a Value>,
) -> Result<(), BackendReadinessError> {
    for operand in operands {
        verify_evidence_value(artifacts, owner, operand)?;
    }
    Ok(())
}

fn verify_evidence_value(
    artifacts: &BackendReadyMirArtifacts,
    owner: FunctionId,
    value: &Value,
) -> Result<(), BackendReadinessError> {
    match value {
        Value::Dictionary(definition) => {
            verify_dictionary_reference(artifacts, owner, *definition)?;
            if let Some(metadata) = artifacts.dictionary(*definition)
                && !metadata.capture_schema().is_empty()
            {
                return Err(BackendReadinessError::InvalidDictionaryCaptureCount {
                    owner,
                    dictionary: *definition,
                    expected: metadata.capture_schema().len(),
                    actual: 0,
                });
            }
        }
        Value::Subscript(definition) => {
            verify_subscript_reference(artifacts, owner, *definition)?;
            if let Some(metadata) = artifacts.subscript(*definition)
                && !metadata.capture_schema().is_empty()
            {
                return Err(BackendReadinessError::InvalidSubscriptCaptureCount {
                    owner,
                    subscript: *definition,
                    expected: metadata.capture_schema().len(),
                    actual: 0,
                });
            }
        }
        Value::Evidence(evidence) => verify_static_evidence(artifacts, owner, evidence)?,
        _ => {}
    }
    Ok(())
}

fn verify_static_evidence(
    artifacts: &BackendReadyMirArtifacts,
    owner: FunctionId,
    evidence: &StaticEvidence,
) -> Result<(), BackendReadinessError> {
    try_for_each_static_evidence(evidence, &mut |evidence| match evidence {
        StaticEvidence::Dictionary {
            definition,
            captures,
        } => {
            verify_dictionary_reference(artifacts, owner, *definition)?;
            if let Some(metadata) = artifacts.dictionary(*definition)
                && captures.len() != metadata.capture_schema().len()
            {
                return Err(BackendReadinessError::InvalidDictionaryCaptureCount {
                    owner,
                    dictionary: *definition,
                    expected: metadata.capture_schema().len(),
                    actual: captures.len(),
                });
            }
            Ok(())
        }
        StaticEvidence::Subscript {
            definition,
            captures,
        } => {
            verify_subscript_reference(artifacts, owner, *definition)?;
            if let Some(metadata) = artifacts.subscript(*definition)
                && captures.len() != metadata.capture_schema().len()
            {
                return Err(BackendReadinessError::InvalidSubscriptCaptureCount {
                    owner,
                    subscript: *definition,
                    expected: metadata.capture_schema().len(),
                    actual: captures.len(),
                });
            }
            Ok(())
        }
        StaticEvidence::VariantPayloadStorage(_) => Ok(()),
    })
}

fn verify_dictionary_reference(
    artifacts: &BackendReadyMirArtifacts,
    owner: FunctionId,
    dictionary: TraitDictionaryId,
) -> Result<(), BackendReadinessError> {
    if artifacts.dictionaries.contains_reference(dictionary) {
        Ok(())
    } else {
        Err(BackendReadinessError::UnresolvedDictionaryReference { owner, dictionary })
    }
}

fn verify_subscript_reference(
    artifacts: &BackendReadyMirArtifacts,
    owner: FunctionId,
    subscript: SubscriptId,
) -> Result<(), BackendReadinessError> {
    if artifacts.subscripts.contains_reference(subscript) {
        Ok(())
    } else {
        Err(BackendReadinessError::UnresolvedSubscriptReference { owner, subscript })
    }
}

fn static_dictionary_definition(
    value: &Value,
    constructed_dictionaries: &FxHashMap<ValueId, TraitDictionaryId>,
) -> Option<TraitDictionaryId> {
    match value {
        Value::Dictionary(definition) => Some(*definition),
        Value::Evidence(evidence) => match evidence.as_ref() {
            StaticEvidence::Dictionary { definition, .. } => Some(*definition),
            _ => None,
        },
        Value::Register(register) => constructed_dictionaries.get(register).copied(),
        _ => None,
    }
}

fn static_subscript(
    value: &Value,
    constructed: &FxHashMap<ValueId, ConstructedSubscript>,
) -> Option<ConstructedSubscript> {
    match value {
        Value::Subscript(definition) => Some(ConstructedSubscript {
            definition: *definition,
            capture_count: 0,
        }),
        Value::Evidence(evidence) => match evidence.as_ref() {
            StaticEvidence::Subscript {
                definition,
                captures,
            } => Some(ConstructedSubscript {
                definition: *definition,
                capture_count: captures.len(),
            }),
            _ => None,
        },
        Value::Register(register) => constructed.get(register).copied(),
        _ => None,
    }
}

fn verify_direct_call(
    artifacts: &BackendReadyMirArtifacts,
    owner: FunctionId,
    operation: &Operation,
) -> Result<(), BackendReadinessError> {
    let (ty, projection) = match &operation.kind {
        OperationKind::Call { ty, .. } => (ty, false),
        OperationKind::Project { ty, .. } => (ty, true),
        _ => return Ok(()),
    };
    let Some(Value::Function(target)) = operation.operands.first() else {
        return Ok(());
    };
    if let Some(signature) = artifacts.native_signature(*target) {
        let expected = signature.parameters.len() + 1;
        let actual = operation.operands.len() - 1;
        if actual != expected {
            return Err(BackendReadinessError::InvalidPhysicalCall {
                owner,
                target: *target,
                expected,
                actual,
            });
        }
        let mut definition =
            CallableDefinition::new_infer_quantifiers(ty.fn_ty.clone(), [], "physical native call");
        definition.result_convention = ty.result_convention;
        if let NativeResult::Addressor { root, .. } = signature.result {
            definition.result_rooted_in = Some(root);
        }
        signature.validate(&definition).map_err(|error| {
            BackendReadinessError::InvalidNativeEntry {
                function: *target,
                error,
            }
        })?;
        return Ok(());
    }
    if target.module != artifacts.module {
        return Ok(());
    }
    let Some(target_body) = artifacts.get(target.function) else {
        return Ok(());
    };
    let expected = physical_call_arity(target_body, projection).ok_or(
        BackendReadinessError::InvalidPhysicalProtocol {
            function: *target,
            reason: "entry requires exactly one trailing result parameter",
        },
    )?;
    // Semantic can_satisfy allows adaptation; it does not make value storage, pointer-result
    // storage, and the yield protocol interchangeable. A direct physical call uses the entry's
    // actual convention; any widening must already be expressed by surrounding code/an adapter.
    if ty.result_convention != target_body.result_convention() {
        return Err(BackendReadinessError::InvalidPhysicalCallConvention {
            owner,
            target: *target,
            expected: target_body.result_convention(),
            actual: ty.result_convention,
        });
    }
    let actual = operation.operands.len() - 1;
    if actual != expected {
        return Err(BackendReadinessError::InvalidPhysicalCall {
            owner,
            target: *target,
            expected,
            actual,
        });
    }
    Ok(())
}

fn verify_local_function_operands<'a>(
    module: ModuleId,
    entry_count: usize,
    owner: FunctionId,
    operands: impl Iterator<Item = &'a Value>,
) -> Result<(), BackendReadinessError> {
    for operand in operands {
        let Value::Function(target) = operand else {
            continue;
        };
        verify_local_function_target(module, entry_count, owner, *target)?;
    }
    Ok(())
}

fn verify_local_function_target(
    module: ModuleId,
    entry_count: usize,
    owner: FunctionId,
    target: FunctionId,
) -> Result<(), BackendReadinessError> {
    if target.module == module && target.function.as_index() >= entry_count {
        return Err(BackendReadinessError::InvalidPhysicalEntry { owner, target });
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::program::{InternedStaticEvidence, PhysicalProgramError, resolve_physical_program};
    use std::convert::identity;
    use ustr::ustr;

    use crate::{
        CompilerSession, ExecutionTarget,
        compiler::MirOptimization,
        hir::native_functions::NativeOptionalFnN,
        module::{
            Module, ModuleEnv, Path, SubscriptDefinition, SubscriptMember, SubscriptSignature,
            TraitDictionaryEntry, Visibility, YieldProvenance,
        },
        std::{
            STD_MODULE_ID, buffer::INVALID_BUFFER_CLONE, math::int_type, option::option_type,
            ordering::ordering_type,
        },
        types::effects::no_effects,
        types::{r#type::SubscriptType, type_like::TypeLike},
    };

    use super::*;

    fn compile(session: &mut CompilerSession, source: &str, name: &str) -> ModuleId {
        session
            .compile(source, name, Path::single_str(name))
            .expect("test module should compile")
            .module_id
    }

    fn lower(
        session: &mut CompilerSession,
        module: ModuleId,
    ) -> Result<(BackendReadyMirArtifacts, LocalFunctionId), BackendReadinessError> {
        session.set_mir_optimization(MirOptimization::Enabled);
        session.prepare_execution_target(ExecutionTarget::Mir, module);
        let semantic = session
            .mir_artifacts_for(module, MirOptimization::Enabled)
            .expect("optimized MIR was just prepared");
        let first_helper = LocalFunctionId::from_index(semantic.entry_count());
        let known = session.known_callees();
        let physical = lower_physical_mir(
            module,
            semantic,
            ModuleEnv::new(session.expect_fresh_module(module), session.raw_modules()),
            known,
        )?;
        Ok((physical, first_helper))
    }

    #[test]
    #[should_panic(expected = "does not dominate")]
    fn physical_boundary_rejects_use_before_definition() {
        let mut session = CompilerSession::new();
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new("bad_dominance".into(), CallResultConvention::Value);
        builder.add_parameter(int_type(), ParameterKind::Return);
        let block = builder.add_block();
        let slot = builder
            .append_operation(block, Operation::alloca(span, int_type()))
            .unwrap();
        builder.append_operation(block, Operation::load(span, slot));
        builder.set_terminator(block, Terminator::ret(span));
        let mut edit = FunctionEdit::new(builder.finish_unverified());
        edit.block_mut(block).operations.swap(0, 1);
        verify_test_body(&mut session, edit.finish_unverified());
    }

    #[test]
    #[should_panic(expected = "propagate_error requires one in-flight source failure")]
    fn physical_boundary_rejects_invalid_failure_flow() {
        let mut session = CompilerSession::new();
        let mut builder = FunctionBuilder::new("bad_failure".into(), CallResultConvention::Value);
        builder.add_parameter(Type::unit(), ParameterKind::Return);
        let block = builder.add_block();
        builder.set_terminator(
            block,
            Terminator::propagate_error(Location::new_synthesized()),
        );
        verify_test_body(&mut session, builder.finish_unverified());
    }

    #[test]
    #[should_panic(expected = "frame exits with live owned register")]
    fn physical_boundary_rejects_owned_register_leaks() {
        let mut session = CompilerSession::new();
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new("bad_ownership".into(), CallResultConvention::Value);
        builder.add_parameter(Type::unit(), ParameterKind::Return);
        let extent = Value::Constant(builder.add_constant(
            int_type(),
            LiteralValue::new_native(8isize),
            &session.module_env(),
        ));
        let block = builder.add_block();
        builder.append_operation(
            block,
            Operation::runtime_alloc(span, int_type(), extent.clone(), extent),
        );
        builder.set_terminator(block, Terminator::ret(span));
        verify_test_body(&mut session, builder.finish_unverified());
    }

    #[test]
    #[should_panic(
        expected = "stored operand must be a value or place pointer, got BorrowedCallable"
    )]
    fn physical_boundary_rejects_borrowed_callable_escape() {
        let mut session = CompilerSession::new();
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new("bad_borrow".into(), CallResultConvention::Value);
        let receiver =
            Value::Parameter(builder.add_parameter(Type::unit(), ParameterKind::Dictionary));
        let result = Value::Parameter(builder.add_parameter(Type::unit(), ParameterKind::Return));
        let block = builder.add_block();
        let borrowed = builder
            .append_operation(
                block,
                Operation::borrow_subscript_member(span, receiver, false, Type::unit()),
            )
            .unwrap();
        let store = builder
            .append_operation(block, Operation::alloca(span, Type::unit()))
            .unwrap();
        builder.append_operation(block, Operation::store(span, store, result));
        builder.set_terminator(block, Terminator::ret(span));
        // Bypass insertion-time debug checks to exercise the actual artifact boundary.
        let mut edit = FunctionEdit::new(builder.finish_unverified());
        edit.block_mut(block).operations[2].operands[0] = borrowed;
        verify_test_body(&mut session, edit.finish_unverified());
    }

    fn verify_test_body(session: &mut CompilerSession, body: Function) {
        let module = compile(session, "fn anchor() {}", "invalid_physical_body");
        let (mut artifacts, _) = lower(session, module).unwrap();
        artifacts.entries.push(Some(body));
        let env = ModuleEnv::new(session.expect_fresh_module(module), session.raw_modules());
        verify_physical_mir(&artifacts, env).unwrap();
    }

    #[test]
    fn physical_direct_calls_require_the_callee_result_convention() {
        let mut session = CompilerSession::new();
        let module = compile(&mut session, "fn anchor() {}", "call_convention");
        let (mut artifacts, _) = lower(&mut session, module).unwrap();
        let span = Location::new_synthesized();
        let target = FunctionId::new(module, LocalFunctionId::from_index(artifacts.entries.len()));
        let mut callee =
            FunctionBuilder::new("addressor".into(), CallResultConvention::ADDRESSOR_PLACE);
        callee.add_parameter(int_type(), ParameterKind::Return);
        let block = callee.add_block();
        callee.set_terminator(block, Terminator::ret(span));
        artifacts.entries.push(Some(callee.finish_unverified()));
        let owner = FunctionId::new(module, LocalFunctionId::from_index(artifacts.entries.len()));
        let mut caller = FunctionBuilder::new("caller".into(), CallResultConvention::Value);
        let result = Value::Parameter(caller.add_parameter(int_type(), ParameterKind::Return));
        let block = caller.add_block();
        let call = Operation::call(
            span,
            Value::Function(target),
            [result],
            CallImplType::value(FnType::new_by_val([], int_type(), no_effects())),
        );
        // Same arity, different result transport: this used to pass the arity-only checks.
        assert!(matches!(
            verify_direct_call(&artifacts, owner, &call),
            Err(BackendReadinessError::InvalidPhysicalCallConvention { .. })
        ));
        caller.append_operation(block, call);
        caller.set_terminator(block, Terminator::ret(span));
        let caller_module = compile(&mut session, "fn anchor() {}", "foreign_caller");
        let (mut caller_artifacts, _) = lower(&mut session, caller_module).unwrap();
        caller_artifacts
            .entries
            .push(Some(caller.finish_unverified()));
        assert!(matches!(
            resolve_physical_program([&artifacts, &caller_artifacts]),
            Err(PhysicalProgramError::InvalidCallConvention { .. })
        ));
    }

    #[test]
    fn physical_calls_reject_malformed_later_callee_signatures() {
        for kinds in [
            vec![],
            vec![ParameterKind::Parameter(ArgConvention::MutableRef)],
            vec![ParameterKind::Return, ParameterKind::Return],
            vec![
                ParameterKind::Return,
                ParameterKind::Parameter(ArgConvention::MutableRef),
            ],
        ] {
            let mut session = CompilerSession::new();
            let module = compile(&mut session, "fn anchor() {}", "malformed_callee");
            let (mut artifacts, _) = lower(&mut session, module).unwrap();
            let span = Location::new_synthesized();
            // The caller is checked before the callee's own entry validation.
            let target = FunctionId::new(
                module,
                LocalFunctionId::from_index(artifacts.entries.len() + 1),
            );
            let mut caller =
                FunctionBuilder::new("earlier_caller".into(), CallResultConvention::Value);
            caller.add_parameter(Type::unit(), ParameterKind::Return);
            let block = caller.add_block();
            caller.append_operation(
                block,
                Operation::project(
                    span,
                    Value::Function(target),
                    [],
                    int_type(),
                    CallImplType::new(
                        FnType::new_by_val([], int_type(), no_effects()),
                        CallResultConvention::YIELDED_ONCE,
                    ),
                ),
            );
            caller.set_terminator(block, Terminator::ret(span));
            artifacts.entries.push(Some(caller.finish_unverified()));
            let mut callee =
                FunctionBuilder::new("later_callee".into(), CallResultConvention::YIELDED_ONCE);
            for kind in kinds {
                callee.add_parameter(int_type(), kind);
            }
            let block = callee.add_block();
            callee.set_terminator(block, Terminator::ret(span));
            artifacts.entries.push(Some(callee.finish_unverified()));
            let env = ModuleEnv::new(session.expect_fresh_module(module), session.raw_modules());
            assert!(matches!(verify_physical_mir(&artifacts, env),
                Err(BackendReadinessError::InvalidPhysicalProtocol { function, .. }) if function == target));
            assert!(matches!(resolve_physical_program([&artifacts]),
                Err(PhysicalProgramError::InvalidResultParameter { function }) if function == target));
        }
    }

    #[test]
    fn physical_boundary_rejects_unresolved_operations_including_invoke() {
        for invoked in [false, true] {
            let mut session = CompilerSession::new();
            let module = compile(&mut session, "fn anchor() {}", "unresolved_operation");
            let (mut artifacts, _) = lower(&mut session, module).unwrap();
            let span = Location::new_synthesized();
            let mut builder =
                FunctionBuilder::new("unresolved".into(), CallResultConvention::Value);
            let evidence =
                Value::Parameter(builder.add_parameter(Type::unit(), ParameterKind::Dictionary));
            builder.add_parameter(Type::unit(), ParameterKind::Return);
            let entry = builder.add_block();
            let operation = Operation::subscript_member(span, evidence, false, Type::unit());
            if invoked {
                let normal = builder.add_block();
                let error = builder.add_block();
                builder.set_terminator(entry, Terminator::invoke(span, operation, normal, error));
                builder.set_terminator(normal, Terminator::ret(span));
                builder.set_terminator(error, Terminator::propagate_error(span));
            } else {
                builder.append_operation(entry, operation);
                builder.set_terminator(entry, Terminator::ret(span));
            }
            artifacts.entries.push(Some(builder.finish_unverified()));
            let env = ModuleEnv::new(session.expect_fresh_module(module), session.raw_modules());
            assert!(matches!(
                verify_physical_mir(&artifacts, env),
                Err(BackendReadinessError::UnresolvedPhysicalOperation {
                    operation: "subscript_member",
                    ..
                })
            ));
        }
    }

    #[test]
    fn physical_yield_requires_a_scoped_entry() {
        for convention in [
            CallResultConvention::Value,
            CallResultConvention::YIELDED_ONCE,
        ] {
            let mut session = CompilerSession::new();
            let module = compile(&mut session, "fn anchor() {}", "yield_protocol");
            let (mut artifacts, _) = lower(&mut session, module).unwrap();
            let span = Location::new_synthesized();
            let mut builder = FunctionBuilder::new("yielding".into(), convention);
            let place = Value::Parameter(builder.add_parameter(
                int_type(),
                ParameterKind::Parameter(ArgConvention::MutableRef),
            ));
            builder.add_parameter(int_type(), ParameterKind::Return);
            let entry = builder.add_block();
            let resume = builder.add_block();
            builder.set_terminator(entry, Terminator::r#yield(span, place, resume));
            builder.set_terminator(resume, Terminator::ret(span));
            artifacts.entries.push(Some(builder.finish_unverified()));
            let env = ModuleEnv::new(session.expect_fresh_module(module), session.raw_modules());
            let result = verify_physical_mir(&artifacts, env);
            if convention == CallResultConvention::YIELDED_ONCE {
                result.unwrap();
            } else {
                assert!(matches!(
                    result,
                    Err(BackendReadinessError::InvalidPhysicalProtocol {
                        reason: "yield requires a scoped accessor entry",
                        ..
                    })
                ));
            }
        }
    }

    #[test]
    fn physical_lowering_preserves_adapted_addressor_call_protocols() {
        let mut session = CompilerSession::new();
        session.set_allow_experimental(true);
        let module = compile(
            &mut session,
            r#"
            subscript first(values: &mut [int]) -> int { ref mut { values[0] } }
            fn read(slot) -> int {
                let mut values = [9];
                values->[slot]
            }
            fn direct() -> int {
                let mut values = [8];
                values->[first]
            }
            let first_slot = first;
            read(first_slot) + direct()
        "#,
            "adapted_physical_addressor",
        );
        let (artifacts, _) = lower(&mut session, module).unwrap();
        let (std, _) = lower(&mut session, STD_MODULE_ID).unwrap();
        resolve_physical_program([&artifacts, &std]).unwrap();
    }

    #[test]
    fn physical_scoped_projections_check_conventions_and_arity() {
        let mut session = CompilerSession::new();
        let module = compile(&mut session, "fn anchor() {}", "project_convention");
        let (mut artifacts, _) = lower(&mut session, module).unwrap();
        let span = Location::new_synthesized();
        let target = FunctionId::new(module, LocalFunctionId::from_index(artifacts.entries.len()));
        let mut callee = FunctionBuilder::new("scoped".into(), CallResultConvention::YIELDED_ONCE);
        callee.add_parameter(
            int_type(),
            ParameterKind::Parameter(ArgConvention::MutableRef),
        );
        callee.add_parameter(int_type(), ParameterKind::Return);
        let block = callee.add_block();
        callee.set_terminator(block, Terminator::ret(span));
        artifacts.entries.push(Some(callee.finish_unverified()));
        let argument = Value::Parameter(ParameterId::from_index(0));
        let ty = CallImplType::new(
            FnType::new_by_val([int_type()], int_type(), no_effects()),
            CallResultConvention::YIELDED_ONCE,
        );
        let projection = Operation::project(
            span,
            Value::Function(target),
            [argument.clone()],
            int_type(),
            ty.clone(),
        );
        assert!(verify_direct_call(&artifacts, target, &projection).is_ok());
        let mut bad_arity = projection.clone();
        bad_arity.operands = vec![Value::Function(target)].into_boxed_slice();
        assert!(matches!(
            verify_direct_call(&artifacts, target, &bad_arity),
            Err(BackendReadinessError::InvalidPhysicalCall { .. })
        ));
        let call = Operation::call(
            span,
            Value::Function(target),
            [argument.clone(), argument],
            ty,
        );
        assert!(matches!(
            verify_physical_operation(
                &artifacts,
                target,
                &FxHashMap::default(),
                &FxHashMap::default(),
                &call
            ),
            Err(BackendReadinessError::InvalidPhysicalProtocol {
                reason: "scoped accessor requires project, not call",
                ..
            })
        ));
    }

    #[test]
    fn physical_boundary_requires_a_result_parameter() {
        let mut session = CompilerSession::new();
        let module = compile(&mut session, "fn anchor() {}", "missing_result");
        let (mut artifacts, _) = lower(&mut session, module).unwrap();
        let mut builder =
            FunctionBuilder::new("missing_result".into(), CallResultConvention::Value);
        let block = builder.add_block();
        builder.set_terminator(block, Terminator::ret(Location::new_synthesized()));
        artifacts.entries.push(Some(builder.finish_unverified()));
        let env = ModuleEnv::new(session.expect_fresh_module(module), session.raw_modules());
        assert!(matches!(
            verify_physical_mir(&artifacts, env),
            Err(BackendReadinessError::InvalidPhysicalProtocol {
                reason: "entry requires exactly one trailing result parameter",
                ..
            })
        ));
    }

    #[test]
    fn native_member_contracts_survive_projection_evidence_and_runtime_matching() {
        use crate::{
            hir::native_functions::{NativeAddressorMut, NativeAddressorRef},
            std::string::String as NativeString,
        };
        unsafe extern "C" fn shared(value: *const NativeString) -> *const NativeString {
            value
        }
        unsafe extern "C" fn mutable(value: *mut NativeString) -> *mut NativeString {
            value
        }
        let mut session = CompilerSession::new();
        let path = Path::single_str("native_members");
        let host_id = session.modules().next_id();
        let mut host = Module::new(host_id, path.clone());
        // SAFETY: identity projections preserve rooting and permit ordinary string mutation.
        unsafe {
            host.add_native_member(
                "native_self".into(),
                Some(NativeAddressorRef::new(shared).description(
                    ["self"],
                    "Shared member",
                    no_effects(),
                )),
                Some(NativeAddressorMut::new(mutable).description(
                    ["self"],
                    "Mutable member",
                    no_effects(),
                )),
            );
        }
        session.register_module(path, host);
        let module = compile(
            &mut session,
            r#"
            fn assign<T>(slot: &mut T, value: T) { slot = value; }
            fn member(value) { value.native_self }
            fn change(value: &mut string) { assign(value.native_self, "changed"); member(value) }
        "#,
            "use_native_members",
        );
        let (physical, _) = lower(&mut session, module).unwrap();
        let (host_physical, _) = lower(&mut session, host_id).unwrap();
        for artifact in [&physical, &host_physical] {
            artifact
                .validate_native_runtime(ModuleEnv::new(
                    session.expect_fresh_module(artifact.module()),
                    session.raw_modules(),
                ))
                .unwrap();
        }
        assert!(
            host_physical
                .native_requirements
                .signatures()
                .any(|signature| matches!(
                    signature.result,
                    NativeResult::Addressor {
                        mutable: false,
                        root: 0,
                        ..
                    }
                ))
        );
        assert!(
            host_physical
                .native_requirements
                .signatures()
                .any(|signature| matches!(
                    signature.result,
                    NativeResult::Addressor {
                        mutable: true,
                        root: 0,
                        ..
                    }
                ))
        );
        let (std, _) = lower(&mut session, STD_MODULE_ID).unwrap();
        resolve_physical_program([&std, &host_physical, &physical]).unwrap();
    }

    #[test]
    fn typed_native_contracts_survive_direct_and_first_class_lowering() {
        use crate::hir::native_functions::{
            NativeLayout, NativeParameter, NativeResult, NativeScalar,
        };
        use crate::std::string::String as NativeString;

        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn size(value: string) { string_len(value) } fn callable() { string_concat }",
            "typed_native",
        );
        let (physical, _) = lower(&mut session, module).unwrap();
        let std = session.std_module();
        let id = |name| {
            FunctionId::new(
                std.module_id(),
                std.get_local_function_id(ustr(name)).unwrap(),
            )
        };
        let size = physical
            .native_signature(id("string_len"))
            .expect("direct entry contract");
        assert_eq!(
            size.parameters,
            [NativeParameter::Shared(NativeLayout::of::<NativeString>())]
        );
        assert_eq!(
            size.result,
            NativeResult::Scalar(NativeLayout::of::<isize>(), NativeScalar::Int)
        );
        let concat = physical
            .native_signature(id("string_concat"))
            .expect("first-class entry contract");
        assert_eq!(
            concat.parameters,
            vec![NativeParameter::Shared(NativeLayout::of::<NativeString>()); 2]
        );
        assert_eq!(
            concat.result,
            NativeResult::Output(NativeLayout::of::<NativeString>())
        );
    }

    #[test]
    fn retained_native_roots_require_entries_and_recheck_their_declarations() {
        use crate::hir::native_functions::NativeFnN;
        let session = CompilerSession::new();
        let module_id = session.modules().next_id();
        let mut module = Module::new(module_id, Path::single_str("native_roots"));
        let local = module.add_function(
            ustr("identity"),
            NativeFnN::from_rust(identity::<isize>).description(["value"], "", no_effects()),
        );
        let function = FunctionId::new(module_id, local);
        let collect = |module: &Module| {
            let env = ModuleEnv::new(module, session.raw_modules());
            let references = PhysicalEvidenceReferences::default();
            let dictionaries =
                PhysicalDictionaryCatalog::from_module(module_id, module, env, &references);
            let subscripts =
                PhysicalSubscriptCatalog::from_module(module_id, module, env, &references);
            collect_native_signatures(
                &[None],
                &dictionaries,
                &subscripts,
                env,
                &buffer::entries(env, session.known_callees()),
            )
        };
        assert!(
            collect(&module).unwrap().contains_key(&function),
            "an unreferenced declared native is still an artifact root"
        );
        module.functions[local.as_index()]
            .definition
            .ty_scheme
            .ty
            .ret = bool_type();
        assert!(matches!(
            collect(&module),
            Err(BackendReadinessError::InvalidNativeEntry {
                error: NativeContractError::ResultType,
                ..
            })
        ));
        module.functions[local.as_index()]
            .definition
            .ty_scheme
            .ty
            .ret = int_type();
        module.functions[local.as_index()]
            .definition
            .ty_scheme
            .ty
            .args[0]
            .ty = Type::variable_id(0);
        assert!(matches!(
            collect(&module),
            Err(BackendReadinessError::InvalidNativeEntry {
                error: NativeContractError::NotClosed,
                ..
            })
        ));

        // Copy a boxed compiler callback under an unrelated host identity. Its std identity,
        // not its signature or name, is what authorizes Buffer expansion.
        let boxed = session
            .std_module()
            .get_function(ustr("buffer_with_capacity"))
            .unwrap();
        module.functions[local.as_index()].code = dyn_clone::clone_box(&*boxed.code);
        assert!(
            matches!(collect(&module), Err(BackendReadinessError::NativeRequirement(
            NativeRequirementError::MissingEntry(id)
        )) if id == function)
        );
    }

    #[test]
    fn typed_native_failure_transport_survives_direct_and_first_class_lowering() {
        use crate::hir::native_functions::{NativeFailureConvention, NativeLayout, NativeResult};
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn quotient(a: int, b: int) { idiv(a, b) } fn callable() { idiv_euclid }",
            "native_failure",
        );
        let (physical, _) = lower(&mut session, module).unwrap();
        let std = session.std_module();
        for name in ["idiv", "idiv_euclid"] {
            let id = FunctionId::new(
                std.module_id(),
                std.get_local_function_id(ustr(name)).unwrap(),
            );
            let signature = physical
                .native_signature(id)
                .expect("fallible entry contract");
            assert_eq!(signature.failure, NativeFailureConvention::StatusWithState);
            assert_eq!(
                signature.result,
                NativeResult::Output(NativeLayout::of::<isize>())
            );
            assert_eq!(
                signature.parameters.len(),
                2,
                "failure state is metadata, not a source argument"
            );
        }
    }

    #[test]
    fn typed_native_lifecycle_contracts_survive_physical_lowering() {
        use crate::hir::native_functions::{NativeLayout, NativeParameter, NativeResult};
        use crate::std::string::String as NativeString;

        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn repeated_len(value: string) { let mut repeated = value; string_push_str(repeated, value); string_len(repeated) }",
            "native_lifecycle",
        );
        let (physical, _) = lower(&mut session, module).unwrap();
        let layout = NativeLayout::of::<NativeString>();
        let has_signature = |parameters, result| {
            physical
                .native_requirements
                .signatures()
                .any(|signature| signature.parameters == parameters && signature.result == result)
        };
        assert!(
            has_signature(
                vec![NativeParameter::Shared(layout)],
                NativeResult::Output(layout)
            ),
            "physical calls must retain the managed clone contract"
        );
        assert!(
            has_signature(vec![NativeParameter::Consuming(layout)], NativeResult::Unit),
            "physical cleanup must retain the consuming drop contract"
        );
    }

    #[test]
    fn native_optional_contract_is_carried_by_function_identity() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn parse(value: string) { parse_int(value) }",
            "native_optional",
        );
        let (physical, _) = lower(&mut session, module).unwrap();
        let std = session.std_module();
        let parse_int = FunctionId::new(
            std.module_id(),
            std.get_local_function_id(ustr("parse_int"))
                .expect("parse_int should be registered"),
        );

        assert_eq!(
            physical.native_optional_payload(parse_int),
            Some(int_type())
        );
    }

    #[test]
    fn native_optional_contract_includes_evidence_catalog_functions() {
        let mut session = CompilerSession::new();
        let module_id = session.modules().next_id();
        let path = Path::single_str("native_optional_evidence");
        let mut module = Module::new(module_id, path.clone());
        let function = NativeOptionalFnN::from_rust(Some::<isize>, option_type(int_type()))
            .description(["value"], "test optional subscript member", no_effects());
        let signature = SubscriptSignature::from_callable_definition(&function.definition);
        let function = module.add_function(ustr("optional_member"), function);
        let mut subscript = SubscriptDefinition::resolved(signature);
        subscript.ref_member = Some(SubscriptMember {
            function,
            provenance: YieldProvenance::YieldedOnce,
        });
        module.add_subscript(ustr("optional_subscript"), subscript, Visibility::Module);
        assert_eq!(session.register_module(path, module), module_id);

        let (physical, _) = lower(&mut session, module_id).unwrap();
        assert_eq!(
            physical.native_optional_payload(FunctionId::new(module_id, function)),
            Some(int_type())
        );
    }

    fn rebuild_evidence_catalogs(
        session: &CompilerSession,
        artifacts: &mut BackendReadyMirArtifacts,
    ) {
        let references = PhysicalEvidenceReferences::collect(&artifacts.entries);
        let source = session.expect_fresh_module(artifacts.module);
        let env = ModuleEnv::new(source, session.raw_modules());
        artifacts.dictionaries =
            PhysicalDictionaryCatalog::from_module(artifacts.module, source, env, &references);
        artifacts.subscripts =
            PhysicalSubscriptCatalog::from_module(artifacts.module, source, env, &references);
        let signatures = collect_native_signatures(
            &artifacts.entries,
            &artifacts.dictionaries,
            &artifacts.subscripts,
            env,
            &buffer::entries(env, session.known_callees()),
        )
        .expect("test evidence-catalog rebuild should preserve native optional contracts");
        artifacts.native_requirements =
            NativeRequirements::collect(&artifacts.entries, &signatures, env)
                .expect("test evidence-catalog rebuild should preserve native requirements");
    }

    #[test]
    fn identity_lowering_retains_every_semantic_entry() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn identity(value: int) -> int { value }",
            "identity",
        );
        let identity = session
            .expect_fresh_module(module)
            .get_local_function_id(ustr("identity"))
            .unwrap();

        let (physical, _) = lower(&mut session, module).unwrap();
        assert_eq!(physical.module(), module);
        assert!(physical.get(identity).is_some());
    }

    #[test]
    fn physical_module_owns_its_relocatable_dictionary_definitions() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "struct Wrapper<A>(A)\nfn wrap<A>(value: A) -> Wrapper<A> { Wrapper(value) }",
            "dictionary_catalog",
        );
        let (physical, _) = lower(&mut session, module).unwrap();
        let source = session.expect_fresh_module(module);

        assert_eq!(physical.dictionaries().len(), source.impl_count());
        assert!(
            physical
                .dictionaries()
                .iter()
                .any(|definition| !definition.capture_schema().is_empty()),
            "the generated Value<Wrapper<A>> dictionary closes over Value<A>"
        );
        for (index, definition) in physical.dictionaries().iter().enumerate() {
            let impl_id = LocalImplId::from_index(index);
            let semantic = &source.get_impl_data(impl_id).unwrap().dictionary_value;
            assert_eq!(definition.id(), TraitDictionaryId::new(module, impl_id));
            assert_eq!(definition.capture_schema(), semantic.capture_schema());
            assert_eq!(definition.entries().len(), semantic.entry_count());
            for (index, entry) in definition.entries().iter().enumerate() {
                let index = TraitDictionaryEntryIndex::from_index(index);
                let TraitDictionaryEntry::Function(function) = semantic.entry(index);
                assert_eq!(entry.function(), FunctionId::new(module, function));
                assert_eq!(
                    entry.capture_mapping(),
                    semantic.entry_capture_mapping(index)
                );
            }
        }
    }

    #[test]
    fn physical_module_owns_its_relocatable_subscript_definitions() {
        let mut session = CompilerSession::new();
        session.set_allow_experimental(true);
        let module = compile(
            &mut session,
            "subscript cell<T>(slot: &mut T) -> T\n\
             where T: Value {\n\
                 ref { let local = slot; yield local }\n\
                 mut { let mut local = slot; yield local; slot = local }\n\
             }\n\
             fn use_cell() { let accessor = cell; let mut value = 3; value->[accessor] }",
            "subscript_catalog",
        );
        let subscript = session
            .expect_fresh_module(module)
            .get_local_subscript_id(ustr("cell"))
            .unwrap();
        let (physical, _) = lower(&mut session, module).unwrap();
        let definition = physical
            .subscript(SubscriptId::new(module, subscript))
            .unwrap();

        assert_eq!(definition.capture_schema().len(), 1);
        let semantic = session
            .expect_fresh_module(module)
            .get_subscript_by_id(subscript)
            .unwrap();
        assert_eq!(
            definition.member(false).unwrap().provenance(),
            semantic.ref_member.as_ref().unwrap().provenance
        );
        assert_eq!(
            definition.member(true).unwrap().provenance(),
            semantic.mut_member.as_ref().unwrap().provenance
        );
        assert_eq!(physical.subscript_imports(), &[]);
    }

    #[test]
    fn physical_subscript_materialization_borrows_members_ephemerally() {
        let mut session = CompilerSession::new();
        session.set_allow_experimental(true);
        let module = compile(
            &mut session,
            "subscript cell<T>(slot: &mut T) -> T where T: Value {\n\
                 ref { let local = slot; yield local }\n\
                 mut { let mut local = slot; yield local; slot = local }\n\
             }\n\
             fn use_cell() {\n\
                 let first = cell;\n\
                 let second = first;\n\
                 let mut value = 3;\n\
                 let before = value->[first];\n\
                 value->[second] + before\n\
             }",
            "subscript_lifecycle",
        );
        let (physical, _) = lower(&mut session, module).unwrap();
        let kinds = physical
            .entries
            .iter()
            .flatten()
            .flat_map(|body| {
                body.blocks().flat_map(|block| {
                    body.block(block)
                        .operations()
                        .iter()
                        .map(|operation| &operation.kind)
                })
            })
            .collect::<Vec<_>>();
        assert!(
            kinds
                .iter()
                .any(|kind| matches!(kind, OperationKind::BuildSubscript { .. }))
        );
        assert!(
            kinds
                .iter()
                .any(|kind| matches!(kind, OperationKind::BorrowSubscriptMember { .. }))
        );
        assert!(
            kinds
                .iter()
                .all(|kind| !matches!(kind, OperationKind::SubscriptMember { .. }))
        );
    }

    #[test]
    fn build_subscript_evidence_appends_captures_before_materialization() {
        let definition = SubscriptId::new(ModuleId::from_index(3), LocalSubscriptId::from_index(4));
        let span = Location::new_synthesized();
        let subscript_ty =
            Type::subscript_type(SubscriptType::new(vec![], Type::unit(), None, None));
        let mut builder =
            FunctionBuilder::new(ustr("subscript_construction"), CallResultConvention::Value);
        let block = builder.add_block();
        let base = Value::Evidence(Box::new(StaticEvidence::Subscript {
            definition,
            captures: vec![StaticEvidence::VariantPayloadStorage(false)].into_boxed_slice(),
        }));
        let extended = builder
            .append_operation(
                block,
                Operation::build_subscript_evidence(
                    span,
                    base,
                    vec![Value::Evidence(Box::new(
                        StaticEvidence::VariantPayloadStorage(true),
                    ))],
                    subscript_ty,
                ),
            )
            .unwrap();
        let materialized = builder
            .append_operation(
                block,
                Operation::build_subscript(span, extended.clone(), subscript_ty),
            )
            .unwrap();
        builder.set_terminator(block, Terminator::ret(span));

        let constructed = constructed_subscript_definitions(&builder.finish_unverified());
        let extended = static_subscript(&extended, &constructed).unwrap();
        assert_eq!(extended.definition, definition);
        assert_eq!(extended.capture_count, 2);
        assert!(static_subscript(&materialized, &constructed).is_none());
    }

    #[test]
    fn a_capture_bearing_subscript_cannot_be_used_bare() {
        let mut session = CompilerSession::new();
        session.set_allow_experimental(true);
        let module = compile(
            &mut session,
            "subscript cell<T>(slot: &mut T) -> T where T: Value {\n\
                 ref { let local = slot; yield local }\n\
             }",
            "bare_subscript",
        );
        let (mut physical, _) = lower(&mut session, module).unwrap();
        let definition = physical
            .subscripts()
            .iter()
            .find(|definition| !definition.capture_schema().is_empty())
            .unwrap()
            .id();
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new(ustr("bare_subscript"), CallResultConvention::Value);
        let block = builder.add_block();
        builder.append_operation(
            block,
            Operation::borrow_subscript_member(
                span,
                Value::Subscript(definition),
                false,
                Type::unit(),
            ),
        );
        builder.set_terminator(block, Terminator::ret(span));
        physical.entries.push(Some(builder.finish_unverified()));

        assert!(matches!(
            verify_physical_mir(&physical, ModuleEnv::new(session.expect_fresh_module(module), session.raw_modules())),
            Err(BackendReadinessError::InvalidSubscriptCaptureCount {
                subscript,
                expected,
                actual: 0,
                ..
            }) if subscript == definition && expected > 0
        ));
    }

    #[test]
    fn selecting_an_absent_subscript_member_is_rejected() {
        let mut session = CompilerSession::new();
        session.set_allow_experimental(true);
        let module = compile(
            &mut session,
            "subscript read_only(slot: &mut int) -> int {\n\
                 ref { let local = slot; yield local }\n\
             }",
            "missing_subscript_member",
        );
        let (mut physical, _) = lower(&mut session, module).unwrap();
        let definition = physical
            .subscripts()
            .iter()
            .find(|definition| definition.member(false).is_some())
            .unwrap()
            .id();
        assert!(
            physical
                .subscript(definition)
                .unwrap()
                .member(true)
                .is_none()
        );
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new(
            ustr("missing_subscript_member"),
            CallResultConvention::Value,
        );
        let block = builder.add_block();
        builder.append_operation(
            block,
            Operation::borrow_subscript_member(
                span,
                Value::Subscript(definition),
                true,
                Type::unit(),
            ),
        );
        builder.set_terminator(block, Terminator::ret(span));
        physical.entries.push(Some(builder.finish_unverified()));

        assert!(matches!(
            verify_physical_mir(&physical, ModuleEnv::new(session.expect_fresh_module(module), session.raw_modules())),
            Err(BackendReadinessError::MissingSubscriptMember {
                subscript,
                mut_member: true,
                ..
            }) if subscript == definition
        ));
    }

    #[test]
    fn whole_program_resolution_rejects_an_unresolved_foreign_subscript() {
        let mut session = CompilerSession::new();
        let module = compile(&mut session, "fn anchor() {}", "unresolved_subscript");
        let (mut physical, _) = lower(&mut session, module).unwrap();
        let foreign = SubscriptId::new(
            ModuleId::from_index(module.as_index() + 1),
            LocalSubscriptId::from_index(0),
        );
        let span = Location::new_synthesized();
        let mut builder =
            FunctionBuilder::new(ustr("unresolved_subscript"), CallResultConvention::Value);
        let block = builder.add_block();
        builder.append_operation(
            block,
            Operation::borrow_subscript_member(
                span,
                Value::Subscript(foreign),
                false,
                Type::unit(),
            ),
        );
        builder.set_terminator(block, Terminator::ret(span));
        physical.entries.push(Some(builder.finish_unverified()));
        rebuild_evidence_catalogs(&session, &mut physical);

        assert!(matches!(
            resolve_physical_program([&physical]),
            Err(PhysicalProgramError::UnresolvedSubscript { subscript, .. })
                if subscript == foreign
        ));
    }

    #[test]
    fn whole_program_resolution_resolves_and_interns_static_evidence() {
        let mut session = CompilerSession::new();
        session.set_allow_experimental(true);
        let module = compile(
            &mut session,
            "subscript cell<T>(slot: &mut T) -> T\n\
             where T: Value { ref { let local = slot; yield local } }\n\
             fn use_cell() { let accessor = cell; let mut value = 3; value->[accessor] }",
            "physical_link",
        );
        let (user, _) = lower(&mut session, module).unwrap();
        let (std, _) = lower(&mut session, STD_MODULE_ID).unwrap();

        let resolved = resolve_physical_program([&user, &std]).unwrap();
        let mut descriptor_indexes = FxHashSet::default();
        for definition in std.dictionaries().iter().chain(user.dictionaries()) {
            let index = resolved.descriptor_index(definition.id()).unwrap();
            assert!(descriptor_indexes.insert(index));
            assert_eq!(resolved.descriptor(index).unwrap().id(), definition.id());
        }

        assert!(resolved.module(STD_MODULE_ID).is_some());
        assert!(resolved.module(module).is_some());
        assert!(
            resolved
                .static_evidence()
                .iter()
                .any(|evidence| matches!(evidence, InternedStaticEvidence::Subscript { .. }))
        );
        assert!(
            resolved
                .static_evidence()
                .iter()
                .any(|evidence| matches!(evidence, InternedStaticEvidence::Dictionary { .. }))
        );
        assert!(resolved.modules().iter().any(|module| {
            module.entries.iter().flatten().any(|function| {
                function.blocks().any(|block| {
                    function.block(block).operations().iter().any(|operation| {
                        operation
                            .operands
                            .iter()
                            .any(|operand| resolved.evidence_id(operand).is_some())
                    })
                })
            })
        }));
    }

    #[test]
    fn whole_program_resolution_resolves_a_foreign_subscript() {
        let mut session = CompilerSession::new();
        session.set_allow_experimental(true);
        let base = compile(
            &mut session,
            "#[private_repr]\n\
             pub struct Secret { inner: [int] }\n\
             pub fn make(value: int) -> Secret { Secret { inner: [value] } }\n\
             pub subscript Secret.value(self) -> int {\n\
                 ref mut { return self.inner[0] }\n\
             }",
            "base",
        );
        let user = compile(
            &mut session,
            "fn read_value<T>(value: &mut T) -> int { value.value }\n\
             fn read() -> int { let mut value = base::make(7); read_value(value) }",
            "user",
        );
        let base_module = session.expect_fresh_module(base);
        assert_eq!(base_module.subscript_count(), 1);
        let subscript = SubscriptId::new(base, LocalSubscriptId::from_index(0));
        let (base_physical, _) = lower(&mut session, base).unwrap();
        let (user_physical, _) = lower(&mut session, user).unwrap();
        let (std, _) = lower(&mut session, STD_MODULE_ID).unwrap();

        assert!(user_physical.subscript_imports().contains(&subscript));
        let resolved = resolve_physical_program([&user_physical, &std, &base_physical]).unwrap();

        assert!(resolved.subscript(subscript).is_some());
        assert!(resolved.subscript_member(subscript, true).is_some());
    }

    #[test]
    fn physical_module_records_foreign_dictionary_references() {
        let mut session = CompilerSession::new();
        let module = compile(&mut session, "fn anchor() {}", "dictionary_import");
        let foreign = TraitDictionaryId::new(STD_MODULE_ID, LocalImplId::from_index(0));
        let nested_foreign = TraitDictionaryId::new(STD_MODULE_ID, LocalImplId::from_index(1));
        let span = Location::new_synthesized();
        let mut builder =
            FunctionBuilder::new(ustr("foreign_dictionary"), CallResultConvention::Value);
        let entry = builder.add_block();
        builder.append_operation(
            entry,
            Operation::dict_entry(
                span,
                Value::Evidence(Box::new(StaticEvidence::Dictionary {
                    definition: foreign,
                    captures: vec![StaticEvidence::bare_dictionary(nested_foreign)]
                        .into_boxed_slice(),
                })),
                TraitDictionaryEntryIndex::from_index(0),
                Type::unit(),
            ),
        );
        builder.set_terminator(entry, Terminator::ret(span));
        let entries = [Some(builder.finish_unverified())];
        let references = PhysicalEvidenceReferences::collect(&entries);
        let source = session.expect_fresh_module(module);
        let env = ModuleEnv::new(source, session.raw_modules());
        let dictionaries = PhysicalDictionaryCatalog::from_module(module, source, env, &references);
        let subscripts = PhysicalSubscriptCatalog::from_module(module, source, env, &references);
        let physical = BackendReadyMirArtifacts {
            module,
            entries: entries.into(),
            native_requirements: NativeRequirements::default(),
            dictionaries,
            subscripts,
        };
        assert_eq!(physical.dictionary_imports(), &[foreign, nested_foreign]);
    }

    #[test]
    fn constructed_dictionary_projection_checks_its_entry_index() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "struct Wrapper<A>(A)\nfn wrap<A>(value: A) -> Wrapper<A> { Wrapper(value) }",
            "constructed_dictionary_entry",
        );
        let (mut physical, _) = lower(&mut session, module).unwrap();
        let definition = physical
            .dictionaries()
            .iter()
            .find(|definition| !definition.capture_schema().is_empty())
            .unwrap();
        let definition_id = definition.id();
        let capture_count = definition.capture_schema().len();
        let invalid_entry = TraitDictionaryEntryIndex::from_index(definition.entries().len());
        let dictionary_ty = session
            .expect_fresh_module(module)
            .get_impl_data(definition_id.impl_id)
            .unwrap()
            .dictionary_ty;

        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new(
            ustr("invalid_dictionary_entry"),
            CallResultConvention::Value,
        );
        let block = builder.add_block();
        let captures = (0..capture_count)
            .map(|_| Value::Evidence(Box::new(StaticEvidence::VariantPayloadStorage(false))))
            .collect();
        let dictionary = builder
            .append_operation(
                block,
                Operation::build_dictionary(span, definition_id, captures, dictionary_ty),
            )
            .unwrap();
        builder.append_operation(
            block,
            Operation::dict_entry(span, dictionary, invalid_entry, Type::unit()),
        );
        builder.set_terminator(block, Terminator::ret(span));
        physical.entries.push(Some(builder.finish_unverified()));
        rebuild_evidence_catalogs(&session, &mut physical);

        assert!(matches!(
            verify_physical_mir(&physical, ModuleEnv::new(session.expect_fresh_module(module), session.raw_modules())),
            Err(BackendReadinessError::InvalidDictionaryEntryIndex {
                dictionary,
                entry,
                ..
            }) if dictionary == definition_id && entry == invalid_entry
        ));
    }

    fn invalid_shell_test_lowerer(
        session: &CompilerSession,
        module: ModuleId,
    ) -> PhysicalLowerer<'_> {
        let helper_base = FunctionId::new(module, LocalFunctionId::from_index(0));
        PhysicalLowerer::new(
            helper_base,
            ModuleEnv::new(session.expect_fresh_module(module), session.raw_modules()),
            session.known_callees(),
        )
    }

    fn append_test_variant_shell(
        builder: &mut FunctionBuilder,
        block: BlockId,
        variant_ty: Type,
    ) -> Value {
        builder
            .append_operation(
                block,
                Operation::variant(
                    Location::new_synthesized(),
                    ustr("Only"),
                    variant_ty,
                    Type::unit(),
                    Some(VariantPayloadStorage::Inline),
                    None,
                    None,
                ),
            )
            .expect("variant produces a shell")
    }

    #[test]
    fn a_variant_shell_must_be_stored_exactly_once() {
        let mut session = CompilerSession::new();
        let module = compile(&mut session, "fn anchor() {}", "duplicate_shell_store");
        let span = Location::new_synthesized();
        let variant_ty = Type::variant([(ustr("Only"), Type::unit())]);
        let mut builder = FunctionBuilder::new(ustr("duplicate"), CallResultConvention::Value);
        let destination =
            Value::Parameter(builder.add_parameter(variant_ty, ParameterKind::Return));
        let entry = builder.add_block();
        let shell = append_test_variant_shell(&mut builder, entry, variant_ty);
        builder.append_operation(
            entry,
            Operation::store(span, shell.clone(), destination.clone()),
        );
        builder.append_operation(entry, Operation::store(span, shell, destination));
        builder.set_terminator(entry, Terminator::ret(span));

        let result = invalid_shell_test_lowerer(&session, module).lower_variant_shell_allocations(
            FunctionId::new(module, LocalFunctionId::from_index(0)),
            builder.finish_unverified(),
        );
        assert!(matches!(
            result,
            Err(BackendReadinessError::InvalidVariantShellStore { .. })
        ));
    }

    #[test]
    fn a_variant_shell_cannot_be_stored_by_an_invoke() {
        let mut session = CompilerSession::new();
        let module = compile(&mut session, "fn anchor() {}", "invoked_shell_store");
        let span = Location::new_synthesized();
        let variant_ty = Type::variant([(ustr("Only"), Type::unit())]);
        let mut builder = FunctionBuilder::new(ustr("invoked"), CallResultConvention::Value);
        let destination =
            Value::Parameter(builder.add_parameter(variant_ty, ParameterKind::Return));
        let entry = builder.add_block();
        let normal = builder.add_block();
        let error = builder.add_block();
        let shell = append_test_variant_shell(&mut builder, entry, variant_ty);
        builder.set_terminator(
            entry,
            Terminator::invoke(
                span,
                Operation::store(span, shell, destination),
                normal,
                error,
            ),
        );
        builder.set_terminator(normal, Terminator::ret(span));
        builder.set_terminator(error, Terminator::propagate_error(span));

        let result = invalid_shell_test_lowerer(&session, module).lower_variant_shell_allocations(
            FunctionId::new(module, LocalFunctionId::from_index(0)),
            builder.finish_unverified(),
        );
        assert!(matches!(
            result,
            Err(BackendReadinessError::InvalidVariantShellStore { .. })
        ));
    }

    #[test]
    fn a_static_product_projection_becomes_a_byte_offset() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn second(value: (bool, int)) -> int { value.1 }",
            "subfield",
        );
        let second = session
            .expect_fresh_module(module)
            .get_local_function_id(ustr("second"))
            .unwrap();
        let (physical, _) = lower(&mut session, module).unwrap();
        let body = physical.get(second).unwrap();
        assert!(body.blocks().any(|block| {
            body.block(block)
                .operations()
                .iter()
                .any(|operation| matches!(operation.kind, OperationKind::AddressOffset { .. }))
        }));
        assert!(
            !body
                .blocks()
                .any(|block| body
                    .block(block)
                    .operations()
                    .iter()
                    .any(|operation| matches!(
                        operation.kind,
                        OperationKind::Subfield {
                            variant_payload: false,
                            ..
                        }
                    )))
        );
    }

    #[test]
    fn equivalent_dynamic_product_addressors_share_one_helper() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn right<A, B>(value: (A, B)) -> B { value.1 }\n\
             fn right_again<A, B>(value: (A, B)) -> B { value.1 }",
            "generic_subfield",
        );
        let (physical, first_helper) = lower(&mut session, module).unwrap();
        assert_eq!(
            physical.entry_count() - first_helper.as_index(),
            1,
            "equivalent product layout recipes should share one generated addressor"
        );
        let helper = physical.get(first_helper).unwrap();
        assert!(helper.blocks().any(|block| {
            helper
                .block(block)
                .operations()
                .iter()
                .any(|operation| matches!(operation.kind, OperationKind::AddressOffset { .. }))
        }));
    }

    #[test]
    fn dynamic_projections_reuse_a_retained_structural_addressor() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn direct<A>(record: { x: int, y: A }) -> A { record.y }\n\
             fn get_y<T>(record: T) { record.y }\n\
             fn forward<A>(record: { x: int, y: A }) -> A { get_y(record) }",
            "retained_addressor",
        );
        let source = session.expect_fresh_module(module);
        let retained = source
            .functions
            .iter()
            .enumerate()
            .find_map(|(index, function)| {
                matches!(
                    function.origin,
                    CallableOrigin::StructuralFieldAddressor { .. }
                )
                .then_some(LocalFunctionId::from_index(index))
            })
            .expect("generic projection evidence must retain a structural addressor");
        let direct = source.get_local_function_id(ustr("direct")).unwrap();
        let (physical, first_helper) = lower(&mut session, module).unwrap();
        assert!(physical.get(retained).is_some());
        assert_eq!(
            physical.entry_count(),
            first_helper.as_index(),
            "reuse the retained body instead of generating a duplicate helper"
        );
        let mut referenced = Vec::new();
        physical
            .get(direct)
            .unwrap()
            .visit_function_ids(|id| referenced.push(id));
        assert!(referenced.contains(&FunctionId::new(module, retained)));
    }

    #[test]
    fn an_open_record_addressor_orders_members_by_runtime_alignment() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn field_a<A>(value: { a: A, b: int }) -> A { value.a }\n\
             fn field_b<A>(value: { a: A, b: int }) -> int { value.b }",
            "generic_record_subfield",
        );
        let (physical, first_helper) = lower(&mut session, module).unwrap();
        assert_eq!(physical.entry_count() - first_helper.as_index(), 2);
        let mut case_counts = (first_helper.as_index()..physical.entry_count())
            .flat_map(|index| {
                let helper = physical.get(LocalFunctionId::from_index(index)).unwrap();
                helper.blocks().filter_map(|block| {
                    let TerminatorKind::SwitchVariant { cases, .. } =
                        &helper.block(block).terminator().kind
                    else {
                        return None;
                    };
                    Some(cases.len())
                })
            })
            .collect::<Vec<_>>();
        case_counts.sort_unstable();
        assert_eq!(case_counts, [1, 2]);

        let mut checked_comparisons = 0;
        for index in first_helper.as_index()..physical.entry_count() {
            let helper = physical.get(LocalFunctionId::from_index(index)).unwrap();
            let comparison_result = helper
                .blocks()
                .flat_map(|block| helper.block(block).operations())
                .find_map(|operation| {
                    let OperationKind::Call { ty, .. } = &operation.kind else {
                        return None;
                    };
                    (ty.ret() == ordering_type())
                        .then(|| operation.operands.last().cloned())
                        .flatten()
                });
            let Some(Value::Register(comparison_result)) = comparison_result else {
                continue;
            };
            checked_comparisons += 1;
            let comparison_slot_ty = helper
                .blocks()
                .flat_map(|block| helper.block(block).operations())
                .find_map(|operation| {
                    (operation.result_id() == Some(comparison_result)).then_some(&operation.kind)
                })
                .and_then(|kind| match kind {
                    OperationKind::Alloca { ty } => Some(*ty),
                    _ => None,
                });
            assert_eq!(comparison_slot_ty, Some(ordering_type()));
        }
        assert_eq!(checked_comparisons, 2);
    }

    #[test]
    fn positional_addressors_only_materialize_layouts_through_the_target() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn middle<A, B>(value: (int, A, B)) -> A { value.1 }",
            "generic_positional_subfield",
        );
        let (physical, first_helper) = lower(&mut session, module).unwrap();
        assert_eq!(physical.entry_count() - first_helper.as_index(), 1);
        let helper = physical.get(first_helper).unwrap();
        let layout_getters = helper
            .blocks()
            .flat_map(|block| helper.block(block).operations())
            .filter(|operation| matches!(operation.kind, OperationKind::DictEntry { .. }))
            .count();
        assert_eq!(
            layout_getters, 1,
            "only the target alignment is needed; its size and B's layout are unused"
        );
    }

    #[test]
    fn compact_addressors_fold_static_member_ordering() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn field_d<A>(value: { a: A, b: int, c: int, d: int }) -> int { value.d }",
            "partially_static_record_subfield",
        );
        let (physical, first_helper) = lower(&mut session, module).unwrap();
        let int_add = session.known_callees().int_add().0;
        assert_eq!(physical.entry_count() - first_helper.as_index(), 1);
        let helper = physical.get(first_helper).unwrap();
        let switches = helper
            .blocks()
            .filter(|block| {
                matches!(
                    helper.block(*block).terminator().kind,
                    TerminatorKind::SwitchVariant { .. }
                )
            })
            .count();
        assert_eq!(
            switches, 1,
            "the static b/c ordering does not require a run-time comparison"
        );
        let additions = helper
            .blocks()
            .flat_map(|block| helper.block(block).operations())
            .filter(|operation| operation.operands.first() == Some(&Value::Function(int_add)))
            .count();
        assert_eq!(
            additions, 1,
            "the sizes of b and c are folded into the initial offset; only A is added conditionally"
        );
    }

    #[test]
    fn generic_product_construction_uses_physical_addressors() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn pair<A, B>(left: A, right: B) -> (A, B) { (left, right) }",
            "generic_product_construction",
        );
        let pair = session
            .expect_fresh_module(module)
            .get_local_function_id(ustr("pair"))
            .unwrap();
        let (physical, first_helper) = lower(&mut session, module).unwrap();
        let body = physical.get(pair).unwrap();

        assert!(
            !body
                .blocks()
                .any(|block| body
                    .block(block)
                    .operations()
                    .iter()
                    .any(|operation| matches!(
                        operation.kind,
                        OperationKind::Subfield {
                            variant_payload: false,
                            ..
                        }
                    )))
        );
        assert_eq!(
            physical.entry_count() - first_helper.as_index(),
            1,
            "field zero has a constant offset and the second open member needs an addressor"
        );
    }

    #[test]
    fn recursive_variant_payloads_allocate_address_and_release_owned_storage() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "enum List { Nil, Cons(int, List) }\n\
             fn make(value: int) -> List { List::Cons(value, List::Nil) }\n\
             fn tail(value: List) -> List {\n\
                 match value { Cons(head, tail) => tail, Nil => List::Nil }\n\
             }",
            "recursive_variant_payload",
        );
        let (physical, first_helper) = lower(&mut session, module).unwrap();
        assert!(
            (first_helper.as_index()..physical.entry_count()).any(|index| {
                let helper = physical.get(LocalFunctionId::from_index(index)).unwrap();
                let kinds = helper
                    .blocks()
                    .flat_map(|block| helper.block(block).operations())
                    .map(|operation| &operation.kind)
                    .collect::<Vec<_>>();
                kinds
                    .iter()
                    .any(|kind| matches!(kind, OperationKind::RuntimeAlloc { .. }))
                    && kinds
                        .iter()
                        .any(|kind| matches!(kind, OperationKind::AddressOffsetPlace { .. }))
            })
        );
        let release = (first_helper.as_index()..physical.entry_count())
            .find_map(|index| {
                let helper = physical.get(LocalFunctionId::from_index(index)).unwrap();
                helper
                    .blocks()
                    .flat_map(|block| helper.block(block).operations())
                    .any(|operation| matches!(operation.kind, OperationKind::RuntimeDealloc))
                    .then_some(FunctionId::new(module, LocalFunctionId::from_index(index)))
            })
            .expect("recursive payload lowering generates a release helper");
        let env = ModuleEnv::new(session.expect_fresh_module(module), session.raw_modules());
        assert!(
            (0..first_helper.as_index()).any(|index| {
                let id = FunctionId::new(module, LocalFunctionId::from_index(index));
                let original = session.hir_identity_of(id, MirOptimization::Enabled);
                if !is_value_drop_function(original, &env) {
                    return false;
                }
                let Some(body) = physical.get(LocalFunctionId::from_index(index)) else {
                    return false;
                };
                body.blocks().any(|block| {
                    body.block(block).operations().iter().any(|operation| {
                        matches!(
                            operation.operands.first(),
                            Some(Value::Function(function)) if *function == release
                        )
                    }) && matches!(body.block(block).terminator().kind, TerminatorKind::Return)
                })
            }),
            "the selected Value::drop implementation releases representation storage"
        );
        assert!(!(0..physical.entry_count()).any(|index| {
            let Some(body) = physical.get(LocalFunctionId::from_index(index)) else {
                return false;
            };
            body.blocks().any(|block| {
                body.block(block)
                    .operations()
                    .iter()
                    .any(|operation| matches!(operation.kind, OperationKind::Subfield { .. }))
            })
        }));
    }

    #[test]
    fn fallible_recursive_payload_initialization_releases_its_allocation() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "enum List { Nil, Cons(int, List) }\n\
             fn make(value: int) -> List {\n\
                 List::Cons(if value == 0 { panic(\"x\") } else { value }, List::Nil)\n\
             }",
            "fallible_recursive_variant_payload",
        );
        let (physical, first_helper) = lower(&mut session, module).unwrap();
        let release = (first_helper.as_index()..physical.entry_count())
            .find_map(|index| {
                let body = physical.get(LocalFunctionId::from_index(index))?;
                body.blocks()
                    .flat_map(|block| body.block(block).operations())
                    .any(|operation| matches!(operation.kind, OperationKind::RuntimeDealloc))
                    .then(|| FunctionId::new(module, LocalFunctionId::from_index(index)))
            })
            .expect("recursive payload lowering generates a release helper");
        let make = (0..first_helper.as_index())
            .find_map(|index| {
                let body = physical.get(LocalFunctionId::from_index(index))?;
                (body.name.as_str() == "make").then_some(body)
            })
            .expect("compiled source contains make");

        assert!(make.blocks().any(|block| {
            let block = make.block(block);
            block.operations().iter().any(|operation| {
                matches!(
                    operation.operands.first(),
                    Some(Value::Function(function)) if *function == release
                )
            })
        }));
        assert!(make.blocks().any(|block| {
            matches!(
                make.block(block).terminator().kind,
                TerminatorKind::PropagateError
            )
        }));
        let release_body = physical.get(release.function).unwrap();
        assert!(
            release_body
                .blocks()
                .flat_map(|block| release_body.block(block).operations())
                .filter(|operation| matches!(operation.kind, OperationKind::IsInitialized))
                .count()
                >= 2,
            "release checks both the variant shell and its owning pointer slot"
        );
    }

    #[test]
    fn inline_variant_payloads_do_not_introduce_runtime_allocation() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "enum MaybeInt { None, Some(int) }\n\
             fn unwrap(value: MaybeInt) -> int {\n\
                 match value { Some(value) => value, None => 0 }\n\
             }",
            "inline_variant_payload",
        );
        let (physical, first_helper) = lower(&mut session, module).unwrap();

        assert!(!(0..physical.entry_count()).any(|index| {
            let Some(body) = physical.get(LocalFunctionId::from_index(index)) else {
                return false;
            };
            body.blocks().any(|block| {
                body.block(block).operations().iter().any(|operation| {
                    matches!(
                        operation.kind,
                        OperationKind::RuntimeAlloc { .. } | OperationKind::RuntimeDealloc
                    )
                })
            })
        }));
        let unwrap = (0..first_helper.as_index())
            .find_map(|index| {
                let body = physical.get(LocalFunctionId::from_index(index))?;
                (body.name.as_str() == "unwrap").then_some(body)
            })
            .expect("compiled source contains unwrap");
        assert!(unwrap.blocks().any(|block| {
            unwrap
                .block(block)
                .operations()
                .iter()
                .any(|operation| matches!(operation.kind, OperationKind::AddressOffset { .. }))
        }));
        assert!(
            !unwrap.blocks().any(|block| {
                unwrap.block(block).operations().iter().any(|operation| {
                    matches!(
                        operation.operands.first(),
                        Some(Value::Function(function))
                            if function.module == module
                                && function.function.as_index() >= first_helper.as_index()
                    )
                })
            }),
            "a static inline payload uses no addressor helper"
        );
    }

    #[test]
    fn open_variant_payload_allocation_and_addressing_share_the_stored_representation_bit() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn wrap(x) { Some(x) }\n\
             fn unwrap_or(value, fallback) {\n\
                 match value { Some(value) => value, None => fallback }\n\
             }",
            "open_variant_payload",
        );
        let (physical, first_helper) = lower(&mut session, module).unwrap();

        let helpers = (first_helper.as_index()..physical.entry_count())
            .map(|index| physical.get(LocalFunctionId::from_index(index)).unwrap())
            .collect::<Vec<_>>();
        let allocation = helpers
            .iter()
            .find(|helper| helper.name.as_str().contains("payload_allocation"))
            .expect("an open construction uses an allocation helper");
        let addressor = helpers
            .iter()
            .find(|helper| helper.name.as_str().contains("payload_addressor"))
            .expect("an open projection uses an addressor helper");
        for helper in [allocation, addressor] {
            assert!(helper.blocks().any(|block| {
                helper.block(block).operations().iter().any(|operation| {
                    matches!(operation.kind, OperationKind::ExtractPayloadIndirection)
                })
            }));
        }
        assert!(allocation.blocks().any(|block| {
            allocation
                .block(block)
                .operations()
                .iter()
                .any(|operation| matches!(operation.kind, OperationKind::RuntimeAlloc { .. }))
        }));
        assert!(!addressor.blocks().any(|block| {
            addressor
                .block(block)
                .operations()
                .iter()
                .any(|operation| matches!(operation.kind, OperationKind::RuntimeAlloc { .. }))
        }));
    }

    #[test]
    fn array_mutation_lowers_every_buffer_operation() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn append_and_pop(array: &mut [int], value: int) -> Option<int> {\n\
                 array_append(array, value);\n\
                 array_pop_back(array)\n\
             }",
            "physical_buffer",
        );
        let (physical, first_helper) = lower(&mut session, module).unwrap();

        let operations = (0..physical.entry_count())
            .filter_map(|index| physical.get(LocalFunctionId::from_index(index)))
            .flat_map(|body| {
                body.blocks()
                    .flat_map(|block| body.block(block).operations())
            })
            .collect::<Vec<_>>();
        assert!(
            operations
                .iter()
                .any(|operation| { matches!(operation.kind, OperationKind::RuntimeAlloc { .. }) })
        );
        assert!(
            operations
                .iter()
                .any(|operation| { matches!(operation.kind, OperationKind::RuntimeDealloc) })
        );
        assert!(
            operations
                .iter()
                .any(|operation| { matches!(operation.kind, OperationKind::MoveBytes { .. }) })
        );
        assert!(
            operations
                .iter()
                .any(|operation| { matches!(operation.kind, OperationKind::AddressOffset { .. }) })
        );
        assert!(
            (first_helper.as_index()..physical.entry_count()).any(|index| {
                physical
                    .get(LocalFunctionId::from_index(index))
                    .is_some_and(|body| body.name.as_str().contains("buffer_drop"))
            }),
            "Buffer drop is redirected to a generated physical release helper"
        );
        assert!(!operations.iter().any(|operation| {
            let Some(Value::Function(callee)) = operation.operands.first() else {
                return false;
            };
            session
                .known_callees()
                .resolve(*callee, |_| None)
                .is_some_and(KnownCallee::is_buffer)
        }));
    }

    #[test]
    fn std_buffer_moves_keep_open_element_types() {
        let mut session = CompilerSession::new();
        let (physical, _) = lower(&mut session, STD_MODULE_ID).unwrap();

        let env = ModuleEnv::new(session.std_module(), session.raw_modules());
        let entries = buffer::entries(env, session.known_callees());
        assert_eq!(
            entries.len(),
            11,
            "all storage, Value and Inspect Buffer entries have lowering"
        );
        for id in entries.keys() {
            assert!(
                physical.get(id.function).is_some(),
                "retained Buffer entry {id:?} needs a physical body"
            );
            assert!(
                physical.native_signature(*id).is_none(),
                "do not dispatch back to a boxed primitive"
            );
        }
        let clone_id = entries
            .iter()
            .find_map(|(id, kind)| matches!(kind, BufferEntry::Clone).then_some(*id))
            .unwrap();
        let clone = physical.get(clone_id.function).unwrap();
        assert_eq!(clone.blocks().count(), 1);
        assert!(clone.block(clone.entry()).operations().is_empty());
        assert!(matches!(
            clone.block(clone.entry()).terminator().kind,
            TerminatorKind::InvariantFailure { message }
                if message.as_str() == INVALID_BUFFER_CLONE
        ));
        physical.validate_native_runtime(env).unwrap();

        let operations = (0..physical.entry_count())
            .filter_map(|index| physical.get(LocalFunctionId::from_index(index)))
            .flat_map(|body| {
                body.blocks()
                    .flat_map(|block| body.block(block).operations())
            })
            .collect::<Vec<_>>();
        assert!(operations.iter().any(|operation| {
            matches!(operation.kind, OperationKind::MoveBytes { ty } if !ty.is_constant())
        }));
        assert!(!operations.iter().any(|operation| {
            let Some(Value::Function(callee)) = operation.operands.first() else {
                return false;
            };
            session
                .known_callees()
                .resolve(*callee, |_| None)
                .is_some_and(KnownCallee::is_buffer)
        }));
    }
}
