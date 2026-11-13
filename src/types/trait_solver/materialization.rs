// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Build and cache selected dictionaries, method thunks, and generated Value entries.

use std::{iter::repeat, rc::Rc};

use ustr::Ustr;

use crate::{
    FxHashSet, Location,
    ast::UnnamedArg,
    compiler::error::InternalCompilationError,
    containers::b,
    hir::{
        CallArgument, FnInstData, Node, NodeArena, NodeKind, StaticApplication,
        dictionary::DictionaryReq,
        emit_value_impl::{function_value_method, generic_value_methods_for_type},
        function::{CallableDefinition, arg_conventions_for_args},
        hir_syn::{get_dictionary, load_local},
        value::LiteralValue,
    },
    internal_compilation_error,
    module::{
        ConcreteTraitImplKey, DictionaryEntryEvidence, DictionaryEntryRequirements, FunctionId,
        LocalDecl, LocalDeclId, LocalFunctionId, LocalImplId, ModuleId, PendingFunctionBody,
        PendingModuleFunction, QualifiedNameEnv, TraitDictionary, TraitId, TraitImpl, TraitImplId,
        TraitImpls, Visibility, build_capturing_dictionary_value, build_dictionary_value,
        dictionary_capture_plan, id::Id,
    },
    std::{
        core_traits_names::VALUE_TRAIT_NAME,
        value::{
            generated_value_evidence_types, generated_value_layout_getter, is_value_trait,
            is_value_trait_for_function_type, value_layout_associated_const_values,
            value_layout_getter_evidence_types,
        },
    },
    types::{
        effects::{EffType, EffectVar},
        r#trait::{Trait, TraitAssociatedConstIndex, TraitDictionaryEntryIndex, TraitMethodIndex},
        r#type::{CallImplType, Type, TypeVar},
        type_inference::substitution::InstSubst,
        type_like::TypeLike,
        type_scheme::{PubTypeConstraint, TypeScheme},
    },
};

use super::{
    DerivedImplSnapshot, TraitSolver,
    canonical::{alpha_canonicalize_types, application_key},
    matching::BlanketCandidate,
    trait_def_from_parts,
};

/// Evidence for the generic call and the canonical hidden arguments of its thunk.
/// Keeping these together prevents materialization and capture planning from
/// disagreeing about the callable entry's ABI.
#[derive(Clone)]
pub(super) struct BlanketMethodRequirements {
    pub(super) callee: Vec<DictionaryReq>,
    pub(super) entry: DictionaryEntryRequirements,
}

impl BlanketMethodRequirements {
    /// The requirements of the entry of a method that asks for `callee`: each of those that
    /// have evidence and that the entry `takes`, once, in the order of its first use.
    pub(super) fn new<'a>(
        callee: Vec<DictionaryReq>,
        takes: impl Fn(&DictionaryReq) -> bool,
        trait_def: impl Fn(TraitId) -> &'a Trait,
    ) -> Self {
        let entry = DictionaryEntryRequirements::canonical(
            callee.iter().filter(|requirement| takes(requirement)),
            trait_def,
        );
        Self { callee, entry }
    }

    /// Where the entry takes each of its requirements from, given where the method takes
    /// each of its own.
    pub(super) fn entry_evidence(
        &self,
        callee_evidence: &[DictionaryEntryEvidence],
    ) -> Vec<DictionaryEntryEvidence> {
        self.entry
            .as_slice()
            .iter()
            .map(|requirement| {
                let argument = self
                    .callee
                    .iter()
                    .position(|asked| asked == requirement)
                    .expect("an entry requirement is one of the method");
                callee_evidence[argument]
            })
            .collect()
    }
}

/// Materialized constants have capture-free literal getters; only method thunks
/// contribute evidence requirements to a blanket implementation's dictionary.
fn blanket_dictionary(
    trait_id: TraitId,
    input_tys: &[Type],
    methods: &[LocalFunctionId],
    associated_const_getters: &[LocalFunctionId],
    requirements: &[BlanketMethodRequirements],
) -> TraitDictionary {
    let (capture_schema, mut entry_capture_mappings) = dictionary_capture_plan(
        trait_id,
        input_tys,
        requirements.iter().map(|requirements| &requirements.entry),
    );
    entry_capture_mappings.extend((0..associated_const_getters.len()).map(|_| Vec::new()));
    build_capturing_dictionary_value(
        methods,
        associated_const_getters,
        capture_schema,
        entry_capture_mappings,
    )
}

pub(super) fn materialized_associated_const_values(
    trait_id: TraitId,
    trait_def: &Trait,
    input_tys: &[Type],
    template_values: &[LiteralValue],
    span: Location,
    solver: &TraitSolver<'_>,
) -> Result<Vec<LiteralValue>, InternalCompilationError> {
    if trait_def.associated_const_count() == 0 {
        return Ok(Vec::new());
    }
    if template_values.len() == trait_def.associated_const_count() {
        return Ok(template_values.to_vec());
    }
    // Temporary special case: blanket impls cannot yet store associated const
    // formulas, so materialized Value dictionaries synthesize layout metadata.
    if is_value_trait(trait_id, trait_def) {
        return Ok(
            value_layout_associated_const_values(input_tys[0], span, solver)?
                .into_iter()
                .map(LiteralValue::new_native)
                .collect(),
        );
    }
    Err(internal_compilation_error!(Internal {
        error: format!(
            "cannot materialize compiler-defined associated consts for trait {}",
            trait_def.name
        ),
        span,
    }))
}

impl<'a> TraitSolver<'a> {
    /// Add a concrete trait implementation from the given code body, for single-function traits.
    pub(crate) fn add_concrete_impl_from_code(
        &mut self,
        body: PendingFunctionBody,
        locals: Vec<LocalDecl>,
        trait_id: TraitId,
        input_types: impl Into<Vec<Type>>,
        output_types: impl Into<Vec<Type>>,
    ) -> LocalImplId {
        let trait_def = trait_def_from_parts(self.current_type_items, self.others, trait_id);
        let input_types = input_types.into();
        let output_types = output_types.into();
        let output_effs = trait_def.impl_output_effs_or_pure_defaults(vec![]);
        let definitions = trait_def.instantiate_for_tys(&input_types, &output_types, &output_effs);
        let definition = definitions
            .into_iter()
            .next()
            .expect("single-function trait should have one method");
        let runtime_arg_count = definition.arg_names.len();
        let function =
            PendingModuleFunction::from_body(definition, body, runtime_arg_count, None, locals);
        let qualified_name_env = QualifiedNameEnv::new(self.current_type_items, self.others);
        self.impls.add_concrete_pending(
            trait_id,
            trait_def,
            input_types,
            output_types,
            output_effs,
            [],
            vec![function],
            &mut self.fn_collector,
            &qualified_name_env,
        )
    }

    pub(crate) fn snapshot_derived_impl_state(&self) -> DerivedImplSnapshot {
        DerivedImplSnapshot {
            concrete_key_to_id: self.impls.concrete_key_to_id.clone(),
            blanket_key_to_id: self.impls.blanket_key_to_id.clone(),
            generated_value_key_to_id: self.impls.generated_value_key_to_id.clone(),
            application_key_to_id: self.impls.application_key_to_id.clone(),
            generated_sources: self.impls.generated_sources.clone(),
            uniform_dictionaries: self.impls.uniform_dictionaries.clone(),
            impl_data_len: self.impls.data.len(),
            new_function_len: self.fn_collector.new_elements.len(),
        }
    }

    pub(crate) fn rollback_derived_impl_state(&mut self, snapshot: DerivedImplSnapshot) {
        self.impls.concrete_key_to_id = snapshot.concrete_key_to_id;
        self.impls.blanket_key_to_id = snapshot.blanket_key_to_id;
        self.impls.generated_value_key_to_id = snapshot.generated_value_key_to_id;
        self.impls.application_key_to_id = snapshot.application_key_to_id;
        self.impls.generated_sources = snapshot.generated_sources;
        self.impls.uniform_dictionaries = snapshot.uniform_dictionaries;
        if self.impls.data.len() != snapshot.impl_data_len {
            Rc::make_mut(&mut self.impls.data).truncate(snapshot.impl_data_len);
        }
        self.fn_collector
            .new_elements
            .truncate(snapshot.new_function_len);
    }

    pub(crate) fn reserve_concrete_impl_from_code_entries(
        &mut self,
        trait_id: TraitId,
        input_types: &[Type],
        output_types: &[Type],
        output_effs: &[EffType],
        associated_const_values: impl Into<Vec<LiteralValue>>,
    ) -> LocalImplId {
        let associated_const_values = associated_const_values.into();
        let trait_def = trait_def_from_parts(self.current_type_items, self.others, trait_id);
        trait_def.validate_impl_shape(
            input_types,
            output_types,
            output_effs,
            associated_const_values.len(),
            trait_def.methods.len(),
        );
        let definitions = trait_def.instantiate_for_tys(input_types, output_types, output_effs);
        let mut methods = Vec::with_capacity(definitions.len());
        let mut tys = Vec::with_capacity(definitions.len());

        for (method_index, definition) in definitions.into_iter().enumerate() {
            let method_index = TraitMethodIndex::from_index(method_index);
            let id = self.fn_collector.next_id();
            let ty = Type::function_type(definition.ty_scheme.ty.clone());
            let name = self
                .qualified_name_env()
                .disambiguated_impl_method_name(
                    trait_id,
                    trait_def,
                    method_index,
                    input_types,
                    output_types,
                    output_effs,
                    0,
                    0,
                    &[],
                )
                .into();
            self.fn_collector
                .reserve_with_visibility(name, Visibility::Module);
            methods.push(id);
            tys.push(ty);
        }

        let associated_const_tys = trait_def.instantiate_associated_const_tys_for_tys(
            input_types,
            output_types,
            output_effs,
        );
        let associated_const_names = self.impl_associated_const_names(
            trait_id,
            input_types,
            output_types,
            output_effs,
            0,
            0,
            &[],
        );
        let associated_const_getters = TraitImpls::bundle_pending_trivial_associated_const_getters(
            &associated_const_values,
            &associated_const_tys,
            &mut self.fn_collector,
            |index| associated_const_names[index],
        );
        let dictionary_ty = TraitImpls::dictionary_ty(tys, associated_const_tys);
        let dictionary_value = build_dictionary_value(&methods, &associated_const_getters);
        let imp = TraitImpl::new(
            trait_id,
            output_types.to_vec(),
            output_effs.to_vec(),
            methods,
            dictionary_value,
            dictionary_ty,
            false,
            None,
        )
        .with_associated_const_values(associated_const_values)
        .with_associated_const_getters(associated_const_getters);
        let key = ConcreteTraitImplKey::new(trait_id, input_types.to_vec());
        self.impls.add_concrete_struct(key, imp)
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn replace_concrete_impl_code_entries(
        &mut self,
        impl_id: LocalImplId,
        trait_id: TraitId,
        input_types: &[Type],
        output_types: &[Type],
        output_effs: &[EffType],
        runtime_requirements: &[DictionaryReq],
        code_entries: impl Into<Vec<(PendingFunctionBody, Vec<LocalDecl>)>>,
    ) {
        let methods = self.impls.data[impl_id.as_index()].methods.clone();
        let trait_def = trait_def_from_parts(self.current_type_items, self.others, trait_id);
        let definitions = trait_def.instantiate_for_tys(input_types, output_types, output_effs);

        let mut code_entries = code_entries.into();
        crate::hir::trait_defaults::complete_pending_methods(
            trait_def,
            &definitions,
            DictionaryReq::new_trait_impl(
                trait_id,
                input_types.to_vec(),
                output_types.to_vec(),
                output_effs.to_vec(),
            ),
            &mut code_entries,
        );

        for ((method_id, definition), (body, locals)) in
            methods.into_iter().zip(definitions).zip(code_entries)
        {
            let runtime_arg_count = definition.arg_names.len();
            let definition = Self::dictionary_entry_definition(
                &definition,
                runtime_requirements,
                body.arena[body.entry_node_id].span,
            );
            self.fn_collector.replace(
                method_id,
                PendingModuleFunction::from_body(definition, body, runtime_arg_count, None, locals),
            );
        }
    }

    /// Whether `requirement` is closed and its application is being solved.
    fn closes_a_cycle(&self, requirement: &DictionaryReq) -> bool {
        let DictionaryReq::TraitImpl {
            trait_id,
            input_tys,
            ..
        } = requirement
        else {
            return false;
        };
        requirement.is_closed_trait_impl()
            && self.solving_stack.contains(&(*trait_id, input_tys.clone()))
    }

    fn blanket_method_requirements(
        &self,
        dictionary: &TraitDictionary,
        method_count: usize,
        prerequisites: &[DictionaryReq],
        self_requirement: DictionaryReq,
    ) -> Vec<BlanketMethodRequirements> {
        (0..method_count)
            .map(|index| {
                let mut requirements = prerequisites.to_vec();
                if dictionary
                    .entry_uses_self_dictionary(TraitDictionaryEntryIndex::from_index(index))
                    && !requirements.contains(&self_requirement)
                {
                    requirements.push(self_requirement.clone());
                }
                // Evidence for an application still being solved closes a cycle of recursive
                // `Value` dictionaries: capturing it would nest them endlessly, so the thunk
                // resolves it itself, once the dictionaries exist.
                BlanketMethodRequirements::new(
                    requirements,
                    |requirement| {
                        *requirement == self_requirement || !self.closes_a_cycle(requirement)
                    },
                    |id| self.trait_def(id),
                )
            })
            .collect()
    }

    fn blanket_method_inst_data(
        blanket_ty_var_count: u32,
        blanket_eff_var_count: u32,
        blanket_instantiation: &InstSubst,
        runtime_requirements: Vec<DictionaryReq>,
        fn_span: Location,
    ) -> Result<FnInstData, InternalCompilationError> {
        // Blanket registration guarantees that every method callable quantifies all blanket type
        // variables in canonical numeric order, including variables visible only in impl
        // constraints and therefore absent from the reconstructed trait method signature.
        let ty_args = (0..blanket_ty_var_count)
            .map(TypeVar::new)
            .map(|quantifier| {
                blanket_instantiation
                    .0
                    .get(&quantifier)
                    .copied()
                    .ok_or_else(|| {
                        internal_compilation_error!(Internal {
                            error: format!(
                                "blanket method type quantifier {quantifier} was not resolved"
                            ),
                            span: fn_span,
                        })
                    })
            })
            .collect::<Result<Vec<_>, _>>()?;
        // Registration likewise quantifies all blanket effect variables, including those visible
        // only in impl constraints.
        let eff_args = (0..blanket_eff_var_count)
            .map(EffectVar::new)
            .map(|quantifier| {
                blanket_instantiation
                    .1
                    .get(&quantifier)
                    .cloned()
                    .ok_or_else(|| {
                        internal_compilation_error!(Internal {
                            error: format!(
                                "blanket method effect quantifier {quantifier} was not resolved"
                            ),
                            span: fn_span,
                        })
                    })
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(FnInstData::new(runtime_requirements, ty_args, eff_args))
    }

    pub(super) fn dictionary_entry_definition(
        definition: &CallableDefinition,
        requirements: &[DictionaryReq],
        span: Location,
    ) -> CallableDefinition {
        if requirements.is_empty() {
            return definition.clone();
        }
        let constraints = requirements
            .iter()
            .map(|requirement| match requirement {
                DictionaryReq::ProjectionSubscript {
                    requirement,
                    field,
                    subscript_ty,
                } => PubTypeConstraint::new_projection_subscript_is(
                    *requirement,
                    span,
                    *field,
                    span,
                    subscript_ty.clone(),
                ),
                DictionaryReq::VariantPayloadIndirection {
                    variant_ty,
                    tag,
                    payload_ty,
                } => PubTypeConstraint::new_type_has_variant(
                    *variant_ty,
                    span,
                    *tag,
                    *payload_ty,
                    span,
                ),
                DictionaryReq::TraitImpl {
                    trait_id,
                    input_tys,
                    output_tys,
                    output_effs,
                } => PubTypeConstraint::new_have_trait(
                    *trait_id,
                    input_tys.clone(),
                    output_tys.clone(),
                    output_effs.clone(),
                    span,
                ),
            })
            .collect();
        let mut definition = definition.clone();
        definition.ty_scheme = TypeScheme::new_infer_quantifiers_with_constraints(
            definition.ty_scheme.ty.clone(),
            constraints,
        );
        definition
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn materialize_blanket_method_thunk(
        &mut self,
        function: LocalFunctionId,
        source_module: Option<ModuleId>,
        definition: &CallableDefinition,
        type_var_count: u32,
        effect_var_count: u32,
        instantiation: &InstSubst,
        requirements: &BlanketMethodRequirements,
        span: Location,
    ) -> Result<PendingModuleFunction, InternalCompilationError> {
        let function = self.function_id(
            source_module.unwrap_or(self.current_type_items.module.id),
            function,
        );
        let inst_data = Self::blanket_method_inst_data(
            type_var_count,
            effect_var_count,
            instantiation,
            requirements.callee.clone(),
            span,
        )?;
        let (body, locals) =
            self.blanket_method_thunk_code_entry(function, definition, &[], inst_data, span)?;
        Ok(PendingModuleFunction::from_body(
            Self::dictionary_entry_definition(definition, requirements.entry.as_slice(), span),
            body,
            definition.arg_names.len(),
            None,
            locals,
        ))
    }

    pub(super) fn blanket_method_thunk_code_entry(
        &mut self,
        function_id: FunctionId,
        definition: &CallableDefinition,
        explicit_runtime_arg_infos: &[(NodeKind, Type)],
        inst_data: FnInstData,
        fn_span: Location,
    ) -> Result<(PendingFunctionBody, Vec<LocalDecl>), InternalCompilationError> {
        let locals = definition.gen_locals_no_bounds(
            repeat(Location::new_synthesized()),
            Location::new_synthesized(),
        );
        let mut body_arena = NodeArena::default();

        let explicit_runtime_args = explicit_runtime_arg_infos
            .iter()
            .map(|(kind, ty)| {
                body_arena.alloc(Node::new(
                    kind.clone(),
                    *ty,
                    EffType::empty(),
                    Location::new_synthesized(),
                ))
            })
            .collect();

        let argument_values = definition
            .ty_scheme
            .ty
            .args
            .iter()
            .enumerate()
            .map(|(arg_i, arg_ty)| {
                let id = LocalDeclId::from_index(arg_i);
                body_arena.alloc(Node::new(
                    load_local(id),
                    arg_ty.ty,
                    EffType::empty(),
                    fn_span,
                ))
            })
            .collect();
        let argument_passing = arg_conventions_for_args(&definition.ty_scheme.ty.args);
        let arguments = CallArgument::from_values_and_passing(argument_values, argument_passing);

        let apply = NodeKind::StaticApply(b(StaticApplication {
            function: function_id,
            function_path: None,
            function_span: fn_span,
            extra_arguments: explicit_runtime_args,
            argument_names: definition.arg_names.clone(),
            argument_name_hint_policy: UnnamedArg::None,
            arguments,
            ty: CallImplType::new(
                definition.ty_scheme.ty.clone(),
                definition.result_convention,
            ),
            inst_data,
        }));
        let apply_id = body_arena.alloc(Node::new(
            apply,
            definition.ty_scheme.ty.ret,
            EffType::empty(),
            fn_span,
        ));
        Ok((PendingFunctionBody::new(body_arena, apply_id), locals))
    }

    pub(crate) fn materialize_generated_value_impl_from_methods(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        span: Location,
        methods: Vec<LocalFunctionId>,
    ) -> Result<(TraitImplId, Type), InternalCompilationError> {
        let canonical_input_tys = alpha_canonicalize_types(input_tys);
        let (method_tys, associated_const_tys, dictionary_ty_for_use) = {
            let trait_def = self.trait_def(trait_id);
            assert_eq!(methods.len(), trait_def.methods.len());
            let definitions = trait_def.instantiate_for_tys(&canonical_input_tys, &[], &[]);
            let method_tys = definitions
                .into_iter()
                .map(|definition| Type::function_type(definition.ty_scheme.ty))
                .collect::<Vec<_>>();
            let associated_const_tys =
                trait_def.instantiate_associated_const_tys_for_tys(&canonical_input_tys, &[], &[]);
            let dictionary_ty_for_use = trait_def.get_dictionary_type_for_tys(input_tys, &[], &[]);
            (method_tys, associated_const_tys, dictionary_ty_for_use)
        };
        if input_tys.iter().all(Type::is_constant) {
            let key = ConcreteTraitImplKey::new(trait_id, input_tys.to_vec());
            if let Some(local_impl_id) = self.impls.concrete().get(&key).copied() {
                return Ok((
                    TraitImplId::new(self.current_type_items.module.id, local_impl_id),
                    dictionary_ty_for_use,
                ));
            }
        }
        if let Some(local_impl_id) = self
            .impls
            .generated_value_key_to_id
            .get(&canonical_input_tys)
            .copied()
        {
            return Ok((
                TraitImplId::new(self.current_type_items.module.id, local_impl_id),
                dictionary_ty_for_use,
            ));
        }
        let associated_const_names =
            self.impl_associated_const_names(trait_id, &canonical_input_tys, &[], &[], 0, 0, &[]);
        let requirements = generated_value_evidence_types(canonical_input_tys[0], self)
            .unwrap_or_default()
            .into_iter()
            .map(|ty| DictionaryReq::new_trait_impl(trait_id, vec![ty], vec![], vec![]))
            .collect::<Vec<_>>();
        let static_values =
            value_layout_associated_const_values(canonical_input_tys[0], span, self).ok();
        let (associated_const_values, associated_const_getters, getter_requirements) =
            if let Some(values) = static_values {
                let values = values
                    .into_iter()
                    .map(LiteralValue::new_native)
                    .collect::<Vec<_>>();
                let getters = TraitImpls::bundle_pending_trivial_associated_const_getters(
                    &values,
                    &associated_const_tys,
                    &mut self.fn_collector,
                    |index| associated_const_names[index],
                );
                let getter_requirements = vec![Vec::new(); getters.len()];
                (values, getters, getter_requirements)
            } else {
                let mut getters = Vec::with_capacity(associated_const_tys.len());
                let mut getter_requirements = Vec::with_capacity(associated_const_tys.len());
                for index in
                    (0..associated_const_tys.len()).map(TraitAssociatedConstIndex::from_index)
                {
                    getter_requirements.push(
                        value_layout_getter_evidence_types(
                            canonical_input_tys[0],
                            index,
                            span,
                            self,
                        )?
                        .into_iter()
                        .map(|ty| DictionaryReq::new_trait_impl(trait_id, vec![ty], vec![], vec![]))
                        .collect(),
                    );
                    let getter =
                        generated_value_layout_getter(canonical_input_tys[0], index, span, self)?;
                    let id = self.fn_collector.next_id();
                    self.fn_collector.push_with_visibility(
                        associated_const_names[index.as_index()],
                        getter,
                        Visibility::Module,
                    );
                    getters.push(id);
                }
                (Vec::new(), getters, getter_requirements)
            };
        let dictionary_ty = TraitImpls::dictionary_ty(method_tys, associated_const_tys);
        let entry_requirements = (0..methods.len())
            .map(|index| {
                let mut entry = requirements.clone();
                // Function-value methods supply their own ne body and need no self evidence.
                if self.trait_def(trait_id).default_methods[index].is_some()
                    && !canonical_input_tys[0].is_function()
                {
                    entry.push(DictionaryReq::new_trait_impl(
                        trait_id,
                        canonical_input_tys.clone(),
                        vec![],
                        vec![],
                    ));
                }
                entry
            })
            .chain(getter_requirements)
            .map(|requirements| {
                DictionaryEntryRequirements::canonical(&requirements, |id| self.trait_def(id))
            })
            .collect::<Vec<_>>();
        let (capture_schema, entry_capture_mappings) =
            dictionary_capture_plan(trait_id, &canonical_input_tys, &entry_requirements);
        let dictionary_value = build_capturing_dictionary_value(
            &methods,
            &associated_const_getters,
            capture_schema,
            entry_capture_mappings,
        );
        let imp = TraitImpl::new(
            trait_id,
            Vec::new(),
            Vec::new(),
            methods,
            dictionary_value,
            dictionary_ty,
            false,
            None,
        )
        .with_associated_const_values(associated_const_values)
        .with_associated_const_getters(associated_const_getters);
        let impl_id = if input_tys.iter().all(Type::is_constant) {
            let key = ConcreteTraitImplKey::new(trait_id, input_tys.to_vec());
            self.impls.add_concrete_struct(key, imp)
        } else {
            let impl_id = self.impls.add_anonymous_dictionary_struct(imp);
            Rc::make_mut(&mut self.impls.generated_value_key_to_id)
                .insert(canonical_input_tys, impl_id);
            impl_id
        };
        Ok((
            TraitImplId::new(self.current_type_items.module.id, impl_id),
            dictionary_ty_for_use,
        ))
    }

    pub(crate) fn materialize_compiler_provided_value_dictionary(
        &mut self,
        arena: &mut NodeArena,
        trait_id: TraitId,
        input_tys: &[Type],
        span: Location,
    ) -> Result<(TraitImplId, Type), InternalCompilationError> {
        // Look through the concrete generated-Value cache before deriving method bodies. The
        // lower-level materializer also checks this key, but by then
        // `generic_value_methods_for_type` has already recursively generated every method. Layout
        // evidence asks for the same ground payload dictionaries frequently, and reserved concrete
        // entries deliberately make this fast path safe for recursive `Value` derivation as well.
        let cached_local_id = if input_tys.iter().all(Type::is_constant) {
            let key = ConcreteTraitImplKey::new(trait_id, input_tys.to_vec());
            self.impls.concrete_key_to_id.get(&key).copied()
        } else {
            // Open dictionaries are alpha-canonical caches whose derivation can still contribute
            // constraints in the caller's inference world. Keep their existing lower-level cache
            // check after method derivation; only ground dictionaries are context-free here.
            None
        };
        if let Some(local_id) = cached_local_id {
            let dictionary_ty =
                self.trait_def(trait_id)
                    .get_dictionary_type_for_tys(input_tys, &[], &[]);
            return Ok((
                TraitImplId::new(self.current_type_items.module.id, local_id),
                dictionary_ty,
            ));
        }

        let trait_def = self.trait_def(trait_id);
        let methods = if is_value_trait_for_function_type(trait_id, trait_def, input_tys, &[]) {
            let method_count = trait_def.methods.len();
            (0..method_count)
                .map(TraitMethodIndex::from_index)
                .map(|method_index| function_value_method(self, method_index, span))
                .collect::<Result<Vec<_>, _>>()?
        } else {
            generic_value_methods_for_type(self, trait_id, input_tys, span, arena)?
        };
        self.materialize_generated_value_impl_from_methods(trait_id, input_tys, span, methods)
    }

    pub(super) fn compiler_provided_value_dictionary_node_kind(
        &mut self,
        arena: &mut NodeArena,
        trait_id: TraitId,
        input_tys: &[Type],
        span: Location,
    ) -> Result<(NodeKind, Type), InternalCompilationError> {
        let (impl_id, dictionary_ty) =
            self.materialize_compiler_provided_value_dictionary(arena, trait_id, input_tys, span)?;
        Ok((get_dictionary(impl_id), dictionary_ty))
    }

    /// Accept a blanket candidate for `solve_impl_actual` by materializing its dictionary, or
    /// return `None` when its runtime requirements fail, to go on to the next candidate.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn materialize_blanket_candidate(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        requested_output_tys: Option<&[Type]>,
        requested_output_effs: Option<&[EffType]>,
        candidate: BlanketCandidate<'_>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<Option<TraitImplId>, InternalCompilationError> {
        let value_trait_id = self.std_trait_id(VALUE_TRAIT_NAME);
        let BlanketCandidate {
            module: imp_module_id,
            impl_id,
            sub_key,
            output_tys,
            output_effs,
            runtime_requirements: resolved_runtime_requirements,
            instantiation: blanket_instantiation,
            ..
        } = candidate;
        let imp_constraints = &sub_key.constraints;
        let imp_ty_var_count = sub_key.ty_var_count;
        let imp_eff_var_count = sub_key.eff_var_count;
        let defaulted_output_effect_vars = FxHashSet::default();

        // Non-Value blanket impls can materialize all constraint dictionaries up front.
        if trait_id != value_trait_id {
            let mut runtime_requirements = self.runtime_requirements_from_resolved(
                &resolved_runtime_requirements,
                imp_constraints,
            );
            Self::close_defaulted_requirement_effect_rows(
                &mut runtime_requirements,
                &defaulted_output_effect_vars,
            );
            if !self.validate_runtime_requirements(
                &resolved_runtime_requirements,
                fn_span,
                arena,
                false,
            )? {
                let rejected = self.reject_if_requirements_fail_on_effects(
                    &resolved_runtime_requirements,
                    input_tys,
                    fn_span,
                );
                rejected?;
                return Ok(None);
            }

            // Succeeded? First get the blanket implementation data and compute the output types.
            let impls = if let Some(module_id) = imp_module_id {
                &self.others.get(module_id).unwrap().module().unwrap().impls
            } else {
                #[allow(clippy::needless_borrow)] // clippy has a bug here as of Rust 1.90
                &self.impls
            };
            let imp = &impls.data[impl_id.as_index()];
            // Self evidence belongs to method execution, not to blanket selection.
            // The selected dictionary supplies it through the existing entry mapping.
            let method_requirements = self.blanket_method_requirements(
                &imp.dictionary_value,
                imp.methods.len(),
                &runtime_requirements,
                DictionaryReq::new_trait_impl(
                    trait_id,
                    input_tys.to_vec(),
                    output_tys.clone(),
                    output_effs.clone(),
                ),
            );

            let associated_const_values = {
                let trait_def =
                    trait_def_from_parts(self.current_type_items, self.others, trait_id);
                materialized_associated_const_values(
                    trait_id,
                    trait_def,
                    input_tys,
                    &imp.associated_const_values,
                    fn_span,
                    self,
                )?
            };

            // Then, for every function in the blanket implementation, if needed create a thunk function
            // importing it and closing over the constraint dictionaries.
            let trait_def = trait_def_from_parts(self.current_type_items, self.others, trait_id);
            let definitions = trait_def.instantiate_for_tys(input_tys, &output_tys, &output_effs);
            let gen_functions = imp.methods.clone(); // clone to avoid borrowing issues
            let mut methods = Vec::with_capacity(gen_functions.len());
            let mut tys = Vec::with_capacity(gen_functions.len());
            for (method_index, (fn_id, def)) in gen_functions.iter().zip(definitions).enumerate() {
                let requirements = &method_requirements[method_index];
                let method_index = TraitMethodIndex::from_index(method_index);
                // Build the concrete function type and hash its signature.
                let fn_ty = Type::function_type(def.ty_scheme.ty.clone());

                // Is the generic function from another module, or do we need to pass constraint dictionaries?
                let id = if requirements.callee.is_empty() && imp_module_id.is_none() {
                    // No, so we can just use the generic function as is.
                    *fn_id
                } else {
                    let function = self.materialize_blanket_method_thunk(
                        *fn_id,
                        imp_module_id,
                        &def,
                        imp_ty_var_count,
                        imp_eff_var_count,
                        &blanket_instantiation,
                        requirements,
                        fn_span,
                    )?;
                    let name = Ustr::from(&format!(
                        "{}-thunk",
                        self.qualified_name_env().disambiguated_impl_method_name(
                            trait_id,
                            trait_def,
                            method_index,
                            input_tys,
                            &output_tys,
                            &output_effs,
                            sub_key.ty_var_count,
                            sub_key.eff_var_count,
                            &sub_key.constraints,
                        )
                    ));
                    let id = self.fn_collector.next_id();
                    self.fn_collector
                        .push_with_visibility(name, function, Visibility::Module);
                    id
                };

                methods.push(id);
                tys.push(fn_ty);
            }

            // Build and insert the implementation.
            let associated_const_tys = trait_def.instantiate_associated_const_tys_for_tys(
                input_tys,
                &output_tys,
                &output_effs,
            );
            let associated_const_names = self.impl_associated_const_names(
                trait_id,
                input_tys,
                &output_tys,
                &output_effs,
                sub_key.ty_var_count,
                sub_key.eff_var_count,
                &sub_key.constraints,
            );
            let associated_const_getters =
                TraitImpls::bundle_pending_trivial_associated_const_getters(
                    &associated_const_values,
                    &associated_const_tys,
                    &mut self.fn_collector,
                    |index| associated_const_names[index],
                );
            let dictionary_ty = TraitImpls::dictionary_ty(tys, associated_const_tys);
            let dictionary_value = blanket_dictionary(
                trait_id,
                input_tys,
                &methods,
                &associated_const_getters,
                &method_requirements,
            );
            let imp = TraitImpl::new(
                trait_id,
                output_tys.clone(),
                output_effs.clone(),
                methods,
                dictionary_value,
                dictionary_ty,
                false,
                None,
            )
            .with_associated_const_values(associated_const_values)
            .with_associated_const_getters(associated_const_getters);
            // A generated dictionary denotes its full application, outputs included: it is
            // indexed by its request and by the outputs it has, so that a later request
            // naming either finds it, and never serves another application.
            let local_impl_id = self.impls.add_anonymous_dictionary_struct(imp);
            let requested_key = application_key(
                trait_id,
                input_tys,
                requested_output_tys,
                requested_output_effs,
            );
            let resulting_key =
                application_key(trait_id, input_tys, Some(&output_tys), Some(&output_effs));
            self.record_generated_source(local_impl_id, imp_module_id, impl_id);
            for key in [requested_key, resulting_key] {
                Rc::make_mut(&mut self.impls.application_key_to_id).insert(key, local_impl_id);
            }

            return Ok(Some(
                self.impl_id(self.current_type_items.module.id, local_impl_id),
            ));
        }

        // Value blanket impls may be recursive, so reserve the concrete impl before
        // materializing any deferred constraint dictionaries.
        let imp = if let Some(module_id) = imp_module_id {
            &self
                .others
                .get(module_id)
                .unwrap()
                .module()
                .unwrap()
                .impls
                .data[impl_id.as_index()]
        } else {
            &self.impls.data[impl_id.as_index()]
        };
        let imp_associated_const_values = imp.associated_const_values.clone();
        let gen_functions = imp.methods.clone();
        let source_dictionary = imp.dictionary_value.clone();
        let associated_const_values = {
            let trait_def = trait_def_from_parts(self.current_type_items, self.others, trait_id);
            materialized_associated_const_values(
                trait_id,
                trait_def,
                input_tys,
                &imp_associated_const_values,
                fn_span,
                self,
            )?
        };
        let materialization_snapshot = self.snapshot_derived_impl_state();
        let local_impl_id = self.reserve_concrete_impl_from_code_entries(
            trait_id,
            input_tys,
            &output_tys,
            &output_effs,
            associated_const_values,
        );
        self.record_generated_source(local_impl_id, imp_module_id, impl_id);

        // Now that recursive self-references can resolve to the reserved impl,
        // materialize the deferred constraint dictionaries.
        let mut runtime_requirements = self
            .runtime_requirements_from_resolved(&resolved_runtime_requirements, imp_constraints);
        Self::close_defaulted_requirement_effect_rows(
            &mut runtime_requirements,
            &defaulted_output_effect_vars,
        );
        let method_requirements = self.blanket_method_requirements(
            &source_dictionary,
            gen_functions.len(),
            &runtime_requirements,
            DictionaryReq::new_trait_impl(
                trait_id,
                input_tys.to_vec(),
                output_tys.clone(),
                output_effs.clone(),
            ),
        );
        if !self.validate_runtime_requirements(
            &resolved_runtime_requirements,
            fn_span,
            arena,
            true,
        )? {
            self.rollback_derived_impl_state(materialization_snapshot);
            let rejected = self.reject_if_requirements_fail_on_effects(
                &resolved_runtime_requirements,
                input_tys,
                fn_span,
            );
            rejected?;
            return Ok(None);
        }

        // Then, for every function in the blanket implementation, if needed create a thunk function
        // importing it and closing over the constraint dictionaries.
        let definitions = trait_def_from_parts(self.current_type_items, self.others, trait_id)
            .instantiate_for_tys(input_tys, &output_tys, &output_effs);
        let functions = gen_functions
            .iter()
            .zip(definitions)
            .zip(&method_requirements)
            .map(|((fn_id, def), requirements)| {
                self.materialize_blanket_method_thunk(
                    *fn_id,
                    imp_module_id,
                    &def,
                    imp_ty_var_count,
                    imp_eff_var_count,
                    &blanket_instantiation,
                    requirements,
                    fn_span,
                )
            })
            .collect::<Result<Vec<_>, InternalCompilationError>>()?;
        let methods = self.impls.data[local_impl_id.as_index()].methods.clone();
        assert_eq!(methods.len(), functions.len());
        for (id, function) in methods.iter().copied().zip(functions) {
            self.fn_collector.replace(id, function);
        }
        let associated_const_getters = self.impls.data[local_impl_id.as_index()]
            .associated_const_getters
            .clone();
        Rc::make_mut(&mut self.impls.data)[local_impl_id.as_index()].dictionary_value =
            blanket_dictionary(
                trait_id,
                input_tys,
                &methods,
                &associated_const_getters,
                &method_requirements,
            );

        Ok(Some(
            self.impl_id(self.current_type_items.module.id, local_impl_id),
        ))
    }
}
