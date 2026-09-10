//! Process-local native requirements, rebuilt when restoring a physical snapshot. Snapshots
//! separately validate build provenance and the pointer-free layout/transport contracts.

use std::fmt;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    hir::native_functions::{
        NativeContractError, NativeEntry, NativeFailureConvention, NativeLayout, NativeParameter,
        NativeResult, NativeSignature,
    },
    mir::{Function, OperationKind, terminator::TerminatorKind},
    module::{ConcreteTraitImplKey, FunctionId, ModuleEnv, id::Id},
    std::{
        buffer::buffer_element_type,
        core_traits_names::VALUE_TRAIT_NAME,
        value::{
            VALUE_ALIGN_ASSOC_CONST_INDEX, VALUE_CLONE_METHOD_INDEX, VALUE_DROP_METHOD_INDEX,
            VALUE_SIZE_ASSOC_CONST_INDEX,
        },
    },
    types::{
        r#type::{Type, TypeKind},
        type_properties::concrete_type_is_trivial_copy,
    },
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum NativeRequirementError {
    MissingEntry(FunctionId),
    UnsupportedRepresentation(Type),
    InvalidLayout(Type),
    MissingLifecycle(Type),
    InvalidLifecycle(Type),
    DuplicateLifecycle(Type),
    InvalidEntry {
        function: FunctionId,
        error: NativeContractError,
    },
    RuntimeEntryMismatch(FunctionId),
}

impl fmt::Display for NativeRequirementError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingEntry(id) => write!(f, "native function {id:?} has no physical entry"),
            Self::UnsupportedRepresentation(ty) => {
                write!(f, "unsupported native representation {ty:?}")
            }
            Self::InvalidLayout(ty) => write!(
                f,
                "native layout does not match its Rust representation: {ty:?}"
            ),
            Self::MissingLifecycle(ty) => write!(
                f,
                "native representation lacks a concrete Value implementation: {ty:?}"
            ),
            Self::InvalidLifecycle(ty) => write!(
                f,
                "native Value layout or clone/drop contract is incompatible: {ty:?}"
            ),
            Self::RuntimeEntryMismatch(id) => write!(
                f,
                "runtime native entry differs from the lowered contract: {id:?}"
            ),
            Self::DuplicateLifecycle(ty) => write!(
                f,
                "multiple concrete Value implementations for native type {ty:?}"
            ),
            Self::InvalidEntry { function, error } => {
                write!(f, "invalid native entry {function:?}: {error}")
            }
        }
    }
}

/// Owning native leaves require their registered lifecycle; representation-copyable leaves need
/// only copying and no-op destruction. Buffer is deliberately absent: it is not an opaque Rust leaf.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct NativeTypeRequirement {
    pub(super) layout: NativeLayout,
    pub(super) lifecycle: Option<(FunctionId, FunctionId)>,
}

#[derive(Default)]
pub(super) struct NativeRequirements {
    pub(super) types: FxHashMap<Type, NativeTypeRequirement>,
    pub(super) entries: FxHashMap<FunctionId, NativeEntry>,
}

impl NativeRequirements {
    pub(super) fn signatures(&self) -> impl Iterator<Item = &NativeSignature> {
        self.entries.values().map(NativeEntry::signature)
    }

    pub(super) fn signature(&self, function: FunctionId) -> Option<&NativeSignature> {
        self.entries.get(&function).map(NativeEntry::signature)
    }

    pub(super) fn collect(
        bodies: &[Option<Function>],
        signatures: &FxHashMap<FunctionId, NativeSignature>,
        env: ModuleEnv<'_>,
    ) -> Result<Self, NativeRequirementError> {
        let mut requirements = Self::default();
        let mut pending = Vec::new();
        for body in bodies.iter().flatten() {
            pending.extend(body.parameters().iter().map(|parameter| parameter.ty));
            pending.extend(body.constants().iter().map(|constant| constant.ty));
            for block in body.blocks() {
                let block = body.block(block);
                for operation in block.operations() {
                    operation_types(&operation.kind, &mut pending);
                }
                if let TerminatorKind::Invoke { operation, .. } = &block.terminator().kind {
                    operation_types(&operation.kind, &mut pending);
                }
            }
        }
        for (&id, signature) in signatures {
            let entry = checked_entry(id, env)?;
            if entry.signature() != signature {
                return Err(NativeRequirementError::RuntimeEntryMismatch(id));
            }
            pending.extend(
                signature
                    .parameters
                    .iter()
                    .map(|parameter| parameter.layout().ty),
            );
            pending.push(signature.result.ty());
            requirements.entries.insert(id, entry);
        }

        let mut seen = FxHashSet::default();
        let mut definitions = FxHashSet::default();
        while let Some(ty) = pending.pop() {
            if !seen.insert(ty) {
                continue;
            }
            // Release the universe read lock before inspecting definitions or interning types.
            let kind = ty.data().clone();
            match kind {
                TypeKind::Native(native) => {
                    if let Some(element) = buffer_element_type(ty) {
                        pending.push(element);
                        continue;
                    }
                    if !native.arguments.is_empty() {
                        return Err(NativeRequirementError::UnsupportedRepresentation(ty));
                    }
                    let rust_type = native
                        .bare_ty
                        .value_type_id()
                        .ok_or(NativeRequirementError::UnsupportedRepresentation(ty))?;
                    let layout = NativeLayout {
                        ty,
                        rust_type,
                        size: native.bare_ty.value_size(),
                        align: native.bare_ty.value_align(),
                    };
                    if !layout.align.is_power_of_two()
                        || !layout.size.is_multiple_of(layout.align)
                        || u32::try_from(layout.size).is_err()
                        || u32::try_from(layout.align).is_err()
                    {
                        return Err(NativeRequirementError::InvalidLayout(ty));
                    }
                    let lifecycle = lifecycle(layout, env)?;
                    if let Some((clone, drop)) = lifecycle {
                        requirements
                            .entries
                            .insert(clone, checked_entry(clone, env)?);
                        requirements.entries.insert(drop, checked_entry(drop, env)?);
                    }
                    requirements
                        .types
                        .insert(ty, NativeTypeRequirement { layout, lifecycle });
                }
                TypeKind::Named(named) => {
                    pending.extend(named.params.iter().copied());
                    if definitions.insert(named.def) {
                        let definition = env
                            .try_type_def(named.def)
                            .ok_or(NativeRequirementError::UnsupportedRepresentation(ty))?;
                        // Inspect the generic shape once. Arguments are independently inspected,
                        // avoiding unbounded expansion of recursive named types.
                        pending.push(definition.shape.ty);
                    }
                }
                TypeKind::Tuple(fields) => pending.extend(fields.iter().copied()),
                TypeKind::Record(fields) | TypeKind::Variant(fields) => {
                    pending.extend(fields.iter().map(|(_, ty)| *ty));
                }
                TypeKind::Function(function) => {
                    pending.extend(function.args.iter().map(|arg| arg.ty));
                    pending.push(function.ret);
                }
                TypeKind::Subscript(subscript) => {
                    pending.extend(subscript.args.iter().map(|arg| arg.ty));
                    pending.push(subscript.ret);
                }
                TypeKind::Variable(_) | TypeKind::Never => {}
            }
        }
        for entry in requirements.entries.values() {
            for layout in entry
                .signature()
                .parameters
                .iter()
                .map(|parameter| parameter.layout())
                .chain(result_layout(entry.signature().result))
            {
                if requirements
                    .types
                    .get(&layout.ty)
                    .map(|requirement| requirement.layout)
                    != Some(layout)
                {
                    return Err(NativeRequirementError::InvalidLayout(layout.ty));
                }
            }
        }
        Ok(requirements)
    }

    /// Match against the same process-local runtime, including code identity and optimizer result
    /// guarantees. Equal sizes alone must never authorize linking to another Rust build.
    pub(super) fn validate_runtime(
        &self,
        env: ModuleEnv<'_>,
    ) -> Result<(), NativeRequirementError> {
        for (&id, expected) in &self.entries {
            let actual = checked_entry(id, env)?;
            if actual.address() != expected.address()
                || actual.signature() != expected.signature()
                || actual.result_knowledge() != expected.result_knowledge()
            {
                return Err(NativeRequirementError::RuntimeEntryMismatch(id));
            }
        }
        for (&ty, expected) in &self.types {
            if lifecycle(expected.layout, env)? != expected.lifecycle {
                return Err(NativeRequirementError::InvalidLifecycle(ty));
            }
        }
        Ok(())
    }
}

fn result_layout(result: NativeResult) -> Option<NativeLayout> {
    match result {
        NativeResult::Scalar(layout, _)
        | NativeResult::Addressor {
            pointee: layout, ..
        }
        | NativeResult::Output(layout)
        | NativeResult::Optional {
            payload: layout, ..
        } => Some(layout),
        NativeResult::Unit | NativeResult::Never => None,
    }
}

fn checked_entry(
    id: FunctionId,
    env: ModuleEnv<'_>,
) -> Result<NativeEntry, NativeRequirementError> {
    let function = env
        .module_by_id(id.module)
        .and_then(|module| module.get_function_by_id(id.function))
        .ok_or(NativeRequirementError::MissingEntry(id))?;
    let entry = function
        .code
        .native_entry()
        .ok_or(NativeRequirementError::MissingEntry(id))?;
    entry
        .signature()
        .validate(&function.definition)
        .map_err(|error| NativeRequirementError::InvalidEntry {
            function: id,
            error,
        })?;
    Ok(entry.clone())
}

fn lifecycle(
    layout: NativeLayout,
    env: ModuleEnv<'_>,
) -> Result<Option<(FunctionId, FunctionId)>, NativeRequirementError> {
    let ty = layout.ty;
    let key = ConcreteTraitImplKey::new(env.expect_std_trait_id(VALUE_TRAIT_NAME), vec![ty]);
    let mut found = None;
    for module in std::iter::once(env.current).chain(
        env.modules
            .iter()
            .filter_map(|entry| entry.0.module())
            .filter(|module| module.module_id() != env.current.module_id()),
    ) {
        let Some(id) = module.get_concrete_impl_by_key(&key) else {
            continue;
        };
        if found.is_some() {
            return Err(NativeRequirementError::DuplicateLifecycle(ty));
        }
        let implementation = module.get_impl_data(*id).unwrap();
        let invalid = NativeRequirementError::InvalidLifecycle(ty);
        let size = implementation.associated_const_value(VALUE_SIZE_ASSOC_CONST_INDEX);
        let align = implementation.associated_const_value(VALUE_ALIGN_ASSOC_CONST_INDEX);
        if size
            .as_ref()
            .and_then(|value| value.as_primitive_ty::<isize>())
            .copied()
            != isize::try_from(layout.size).ok()
            || align
                .as_ref()
                .and_then(|value| value.as_primitive_ty::<isize>())
                .copied()
                != isize::try_from(layout.align).ok()
        {
            return Err(invalid);
        }
        let method = |index: usize| {
            implementation
                .methods
                .get(index)
                .copied()
                .map(|id| FunctionId::new(module.module_id(), id))
                .ok_or(invalid)
        };
        let clone = method(VALUE_CLONE_METHOD_INDEX.as_index())?;
        let drop = method(VALUE_DROP_METHOD_INDEX.as_index())?;
        let clone_entry = checked_entry(clone, env)?;
        let drop_entry = checked_entry(drop, env)?;
        let clone_signature = clone_entry.signature();
        let valid_clone = match clone_signature.parameters.as_slice() {
            [NativeParameter::Scalar(input, scalar)] => {
                *input == layout && clone_signature.result == NativeResult::Scalar(layout, *scalar)
            }
            [NativeParameter::Shared(input)] => {
                *input == layout
                    && (clone_signature.result == NativeResult::Output(layout)
                        || (ty == Type::unit() && clone_signature.result == NativeResult::Unit))
            }
            _ => false,
        };
        if !valid_clone
            || clone_signature.failure != NativeFailureConvention::Infallible
            || drop_entry.signature().parameters != [NativeParameter::Consuming(layout)]
            || drop_entry.signature().result != NativeResult::Unit
        {
            return Err(invalid);
        }
        found = Some((clone, drop));
    }
    // Compiler-only representation-copyable leaves (currently StaticStr) have no semantic
    // Value implementation. Their registered TrivialCopy contract supplies copy/no-op drop.
    if found.is_none() && !concrete_type_is_trivial_copy(ty, &env) {
        return Err(NativeRequirementError::MissingLifecycle(ty));
    }
    Ok(found)
}

/// Exhaustive so a new operation carrying a type cannot silently escape native verification.
fn operation_types(kind: &OperationKind, types: &mut Vec<Type>) {
    use OperationKind::*;
    match kind {
        Alloca { ty }
        | AddressOffset { ty }
        | DictEntry { ty, .. }
        | BuildDictionary { ty, .. }
        | SubscriptMember { ty, .. }
        | BuildSubscriptEvidence { ty }
        | BuildSubscript { ty }
        | CloneSubscriptEnv { ty }
        | BorrowSubscriptMember { ty, .. }
        | MoveBytes { ty }
        | Clone { ty }
        | Drop { ty }
        | BuildClosure { ty, .. }
        | CloneClosureEnv { ty } => types.push(*ty),
        AllocaPlace { pointing_to } | AddressOffsetPlace { pointing_to } => {
            types.push(*pointing_to)
        }
        RuntimeAlloc { pointee } => types.push(*pointee),
        Call { ty, .. } | Project { ty, .. } => {
            types.extend(ty.fn_ty.args.iter().map(|arg| arg.ty));
            types.push(ty.ret());
            if let Project { yielded, .. } = kind {
                types.push(*yielded);
            }
        }
        Subfield { ty, product, .. } => {
            types.push(*ty);
            if let Some(product) = product {
                types.push(product.aggregate_ty);
                types.extend(product.layout_witness_tys.iter().copied());
            }
        }
        Variant { metadata, .. } => types.extend([metadata.ty, metadata.payload_ty]),
        BuildArray { element_ty } => types.push(*element_ty),
        RuntimeDealloc
        | EndProject
        | CompareEqual
        | Load
        | DropSubscriptEnv
        | ExtractTag
        | ExtractPayloadIndirection
        | IsInitialized
        | Store
        | Clear
        | Memcpy
        | Move
        | Replace
        | StackSave
        | StackRestore
        | CheckCallDepth
        | CheckFuel
        | DropClosureEnv => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        CompilerSession, Location,
        hir::native_functions::NativeFnN,
        mir::{Operation, builder::FunctionBuilder, terminator::Terminator},
        module::{Module, Path},
        std::{buffer::buffer_type, math::int_type, string::String as NativeString},
        types::{
            effects::no_effects,
            r#type::{CallResultConvention, NativeType, bare_native_type},
        },
    };

    fn body_with_storage(ty: Type) -> Vec<Option<Function>> {
        let mut builder =
            FunctionBuilder::new("native_storage".into(), CallResultConvention::Value);
        let block = builder.add_block();
        let span = Location::new_synthesized();
        builder.append_operation(block, Operation::alloca(span, ty));
        builder.set_terminator(block, Terminator::ret(span));
        vec![Some(builder.finish_unverified())]
    }

    #[test]
    fn opaque_storage_retains_lifecycle_even_without_native_calls() {
        let session = CompilerSession::new();
        let env = ModuleEnv::new(session.std_module(), session.raw_modules());
        let ty = Type::primitive::<NativeString>();
        let requirements =
            NativeRequirements::collect(&body_with_storage(ty), &FxHashMap::default(), env)
                .unwrap();
        let requirement = requirements.types.get(&ty).unwrap();
        assert_eq!(requirement.layout, NativeLayout::of::<NativeString>());
        assert!(requirement.lifecycle.is_some());
        assert_eq!(requirements.entries.len(), 2);
        requirements.validate_runtime(env).unwrap();
    }

    #[test]
    fn native_type_arguments_require_explicit_lowering() {
        let session = CompilerSession::new();
        let env = ModuleEnv::new(session.std_module(), session.raw_modules());
        let unsupported = Type::native_type(NativeType::new(
            bare_native_type::<NativeString>(),
            vec![int_type()],
        ));
        assert!(
            matches!(NativeRequirements::collect(&body_with_storage(unsupported), &FxHashMap::default(), env),
            Err(NativeRequirementError::UnsupportedRepresentation(ty)) if ty == unsupported)
        );
        let buffer = buffer_type(Type::variable_id(0));
        let requirements =
            NativeRequirements::collect(&body_with_storage(buffer), &FxHashMap::default(), env)
                .unwrap();
        assert!(
            !requirements.types.contains_key(&buffer),
            "Buffer uses its physical pointer representation, not Rust Vec storage"
        );
    }

    #[test]
    fn unregistered_owning_native_storage_is_rejected() {
        #[derive(Clone)]
        struct Unregistered;
        let session = CompilerSession::new();
        let env = ModuleEnv::new(session.std_module(), session.raw_modules());
        let ty = Type::primitive::<Unregistered>();
        assert!(
            matches!(NativeRequirements::collect(&body_with_storage(ty), &FxHashMap::default(), env),
            Err(NativeRequirementError::MissingLifecycle(actual)) if actual == ty)
        );
    }

    #[test]
    fn value_evidence_must_match_the_rust_layout() {
        let session = CompilerSession::new();
        let env = ModuleEnv::new(session.std_module(), session.raw_modules());
        for ty in [Type::primitive::<NativeString>(), int_type()] {
            let kind = ty.data().clone();
            let TypeKind::Native(native) = kind else {
                unreachable!()
            };
            let layout = NativeLayout {
                ty,
                rust_type: native.bare_ty.value_type_id().unwrap(),
                size: native.bare_ty.value_size(),
                align: native.bare_ty.value_align(),
            };
            assert!(lifecycle(layout, env).unwrap().is_some());
            assert_eq!(
                lifecycle(
                    NativeLayout {
                        size: layout.size + layout.align,
                        ..layout
                    },
                    env
                ),
                Err(NativeRequirementError::InvalidLifecycle(ty))
            );
            assert_eq!(
                lifecycle(
                    NativeLayout {
                        align: layout.align * 2,
                        ..layout
                    },
                    env
                ),
                Err(NativeRequirementError::InvalidLifecycle(ty))
            );
        }
    }

    #[test]
    fn runtime_matching_checks_code_identity_not_just_layouts() {
        let session = CompilerSession::new();
        let mut module = Module::new(
            session.modules().next_id(),
            Path::single_str("native_runtime"),
        );
        let function = module.add_function(
            "identity".into(),
            NativeFnN::from_rust(std::convert::identity::<isize>).description(
                ["value"],
                "",
                no_effects(),
            ),
        );
        let id = FunctionId::new(module.module_id(), function);
        let signature = module.functions[function.as_index()]
            .code
            .native_entry()
            .unwrap()
            .signature()
            .clone();
        let requirements = NativeRequirements::collect(
            &[],
            &FxHashMap::from_iter([(id, signature)]),
            ModuleEnv::new(&module, session.raw_modules()),
        )
        .unwrap();
        requirements
            .validate_runtime(ModuleEnv::new(&module, session.raw_modules()))
            .unwrap();
        module.functions[function.as_index()].code =
            Box::new(NativeFnN::from_rust(|value: isize| value.wrapping_add(1)));
        assert_eq!(
            requirements.validate_runtime(ModuleEnv::new(&module, session.raw_modules())),
            Err(NativeRequirementError::RuntimeEntryMismatch(id))
        );
        module.functions[function.as_index()]
            .definition
            .ty_scheme
            .ty
            .ret = Type::primitive::<bool>();
        assert_eq!(
            requirements.validate_runtime(ModuleEnv::new(&module, session.raw_modules())),
            Err(NativeRequirementError::InvalidEntry {
                function: id,
                error: NativeContractError::ResultType
            })
        );
        module.functions[function.as_index()]
            .definition
            .ty_scheme
            .ty
            .ret = Type::variable_id(0);
        assert_eq!(
            requirements.validate_runtime(ModuleEnv::new(&module, session.raw_modules())),
            Err(NativeRequirementError::InvalidEntry {
                function: id,
                error: NativeContractError::NotClosed
            })
        );
    }

    #[test]
    fn duplicate_native_value_implementations_report_a_coherence_error() {
        let session = CompilerSession::new();
        let std = session.std_module();
        let env = ModuleEnv::new(std, session.raw_modules());
        let trait_id = env.expect_std_trait_id(VALUE_TRAIT_NAME);
        let key = ConcreteTraitImplKey::new(trait_id, vec![int_type()]);
        let implementation = std
            .get_impl_data(*std.get_concrete_impl_by_key(&key).unwrap())
            .unwrap();
        let mut module = Module::new(
            session.modules().next_id(),
            Path::single_str("duplicate_value"),
        );
        module.add_concrete_impl_for_trait_def_no_locals(
            trait_id,
            std.get_trait_str(VALUE_TRAIT_NAME).unwrap(),
            [int_type()],
            [],
            implementation.associated_const_values.clone(),
            implementation
                .methods
                .iter()
                .map(|id| std.get_function_by_id(*id).unwrap().code.clone())
                .collect::<Vec<_>>(),
        );
        assert_eq!(
            lifecycle(
                NativeLayout::of::<isize>(),
                ModuleEnv::new(&module, session.raw_modules())
            ),
            Err(NativeRequirementError::DuplicateLifecycle(int_type()))
        );
    }
}
