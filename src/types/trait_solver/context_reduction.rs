// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Definition-site context reduction. Unlike ordinary solving, selection here must hold for
//! every instantiation of the enclosing inputs. Evidence is built in the defining body, from
//! the public leaves of the reduction, rather than searched for again in a consumer's scope.

use std::{
    hash::{Hash, Hasher},
    mem,
    rc::Rc,
};

use itertools::Itertools;
use ustr::Ustr;

use crate::{
    FxHashMap, FxHashSet, Location,
    compiler::error::InternalCompilationError,
    hir::{
        FnInstData, NodeArena, dictionary::DictionaryReq,
        emit_hir::instantiate_function_descr_in_place, function::CallableDefinition,
    },
    internal_compilation_error,
    module::{
        DefKind, DictionaryEntryRequirements, ModuleId, PendingModuleFunction, SubscriptId,
        TraitId, TraitImpl, TraitImplId, TraitImpls, TypeDefId, Visibility,
        build_capturing_dictionary_value, dictionary_capture_plan, id::Id,
        named_modules_in_environment,
    },
    std::{core_traits_names::VALUE_TRAIT_NAME, value::generated_value_evidence_types},
    types::{
        effects::{EffType, EffectVar},
        r#trait::TraitDictionaryEntryIndex,
        r#type::{FnType, SubscriptType, Type, TypeKind, TypeVar},
        type_inference::{substitution::InstSubst, unify::UnifiedTypeInference},
        type_like::{TypeLike, instantiate_types},
        type_mapper::{BitmapInstantiationMapper, EffectErasingMapper, TypeMapper},
        type_scheme::{PubTypeConstraint, TypeScheme},
        type_visitor::{TypeInnerVisitor, collect_ty_vars},
    },
};

use super::{
    TraitSolver,
    canonical::alpha_canonicalize_types_with_instantiation,
    improvement::TraitImprovementCandidate,
    matching::input_heads_may_match,
    materialization::{BlanketMethodRequirements, materialized_associated_const_values},
    probe::{ConstraintAssumptions, TraitSolverProbe},
};

pub(crate) const REDUCTION_WORK_LIMIT: usize = 128;

/// A definition-site choice, in the same variable space as its pending body.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SelectedEvidence {
    pub(crate) dictionary: TraitImplId,
    pub(crate) substitution: InstSubst,
    pub(crate) type_count: u32,
    pub(crate) effect_count: u32,
}

impl Hash for SelectedEvidence {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.dictionary.hash(state);
        self.type_count.hash(state);
        self.effect_count.hash(state);
        for entry in self.substitution.0.iter().sorted_by_key(|(var, _)| **var) {
            entry.hash(state);
        }
        for entry in self.substitution.1.iter().sorted_by_key(|(var, _)| **var) {
            entry.hash(state);
        }
    }
}

/// Indices are stable across substitutions and the final ordering of public parameters.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum EvidencePlanSource {
    Pending,
    Public,
    Selected {
        application: SelectedEvidence,
        captures: Vec<usize>,
    },
    /// A reference to this node denotes the generated entries' SelfDictionary parameter.
    GeneratedValue {
        members: Vec<usize>,
    },
    /// Available inside an ancestor generated dictionary's entries, never an eager capture.
    SelfReference {
        target: usize,
    },
    Ground(TraitImplId),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct EvidencePlanNode {
    pub(crate) constraint: PubTypeConstraint,
    pub(crate) source: EvidencePlanSource,
    // The reduction tree owns each obligation; capture edges never search sibling subtrees.
    parent: Option<usize>,
}

/// A use of the subscript that a type declares for a field, as inference made it when it
/// answered a requirement on the field. Its instance is kept, as that of a use by name is in
/// its node: what the subscript requires can be given by the function that makes the use, and
/// the types of the use do not tell the instance then.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct DeclaredFieldUse {
    pub(crate) field: Ustr,
    /// Where the requirement that the use answered was made.
    pub(crate) span: Location,
    /// The type that the requirement asked of the field.
    pub(crate) required: SubscriptType,
    pub(crate) subscript: SubscriptId,
    /// Whether the subscript is of the group being inferred: it has no quantifiers yet, and
    /// its use gets its evidence as a reference to a function of the group does.
    pub(crate) of_group: bool,
    /// What the use gives to the type quantifiers of the subscript, in their order.
    pub(crate) ty_args: Vec<Type>,
    /// What it gives to its effect quantifiers, sorted.
    pub(crate) eff_args: Vec<EffType>,
}

impl DeclaredFieldUse {
    /// Whether this is the use that answered a requirement for `field` on a receiver of type
    /// `receiver_ty` with a result of type `ret`. Effects are left out, as they select nothing.
    pub(crate) fn answers(&self, field: Ustr, receiver_ty: Type, ret: Type) -> bool {
        let erased = |ty: Type| ty.map(&mut EffectErasingMapper);
        self.field == field
            && erased(self.required.receiver_ty()) == erased(receiver_ty)
            && erased(self.required.ret) == erased(ret)
    }
}

/// Compiler-only evidence retained until elaboration. Never part of an exported type scheme.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub(crate) struct EvidencePlan {
    pub(crate) nodes: Vec<EvidencePlanNode>,
    pub(crate) roots: Vec<usize>,
    /// The uses of declared fields that the inference of the function made.
    pub(crate) field_uses: Vec<DeclaredFieldUse>,
}

impl EvidencePlan {
    fn push(&mut self, constraint: PubTypeConstraint, parent: Option<usize>) -> usize {
        let id = self.nodes.len();
        self.nodes.push(EvidencePlanNode {
            constraint,
            source: EvidencePlanSource::Pending,
            parent,
        });
        id
    }

    /// Coalescing outputs can identify previously distinct applications. Check the final graph,
    /// too; only generated Value entries' explicit self edges are construction recursion.
    fn check_construction_cycles(&self) -> Result<(), InternalCompilationError> {
        let mut states = vec![0u8; self.nodes.len()];
        for root in 0..self.nodes.len() {
            let mut pending = vec![(root, false)];
            while let Some((id, finish)) = pending.pop() {
                if finish {
                    states[id] = 2;
                    continue;
                }
                if states[id] == 2 {
                    continue;
                }
                if states[id] == 1 {
                    return Err(unresolved(&self.nodes[id].constraint));
                }
                states[id] = 1;
                pending.push((id, true));
                match &self.nodes[id].source {
                    EvidencePlanSource::Selected { captures, .. } => {
                        pending.extend(captures.iter().rev().map(|child| (*child, false)))
                    }
                    EvidencePlanSource::GeneratedValue { members } => pending.extend(
                        members
                            .iter()
                            .rev()
                            .filter(|child| **child != id)
                            .map(|child| (*child, false)),
                    ),
                    EvidencePlanSource::Pending => {
                        return Err(unresolved(&self.nodes[id].constraint));
                    }
                    EvidencePlanSource::Public
                    | EvidencePlanSource::Ground(_)
                    | EvidencePlanSource::SelfReference { .. } => {}
                }
            }
        }
        Ok(())
    }

    /// Move member construction behind a generated dictionary's entry boundary. The resulting
    /// plan receives its own dictionary as an ordinary parameter, mapped to SelfDictionary by
    /// dictionary_capture_plan. Other ancestor dictionaries remain explicit outer captures.
    pub(crate) fn recursive_entry_plan(&self, root: usize) -> Option<(Self, Vec<usize>)> {
        let EvidencePlanSource::GeneratedValue { members } = &self.nodes[root].source else {
            return None;
        };
        let mut ids = Vec::new();
        let mut indices = FxHashMap::default();
        let mut pending = members.iter().rev().copied().collect::<Vec<_>>();
        let mut recursive = false;
        while let Some(id) = pending.pop() {
            if indices.contains_key(&id) {
                continue;
            }
            indices.insert(id, ids.len());
            ids.push(id);
            if id == root {
                continue;
            }
            match &self.nodes[id].source {
                EvidencePlanSource::Selected { captures, .. } => {
                    pending.extend(captures.iter().rev().copied())
                }
                EvidencePlanSource::GeneratedValue { members } => {
                    pending.extend(members.iter().rev().copied())
                }
                EvidencePlanSource::SelfReference { target } => recursive |= *target == root,
                _ => {}
            }
        }
        if !recursive {
            return None;
        }
        let nodes = ids
            .iter()
            .map(|id| {
                let mut node = self.nodes[*id].clone();
                node.parent = None;
                if *id == root
                    || matches!(node.source, EvidencePlanSource::SelfReference { target }
                    if target == root || !indices.contains_key(&target))
                {
                    node.source = EvidencePlanSource::Public;
                } else {
                    match &mut node.source {
                        EvidencePlanSource::Selected { captures, .. } => {
                            for child in captures {
                                *child = indices[child];
                            }
                        }
                        EvidencePlanSource::GeneratedValue { members } => {
                            for child in members {
                                *child = indices[child];
                            }
                        }
                        EvidencePlanSource::SelfReference { target } => *target = indices[target],
                        _ => {}
                    }
                }
                node
            })
            .collect();
        let roots = members.iter().map(|id| indices[id]).collect();
        Some((
            Self {
                nodes,
                roots,
                field_uses: self.field_uses.clone(),
            },
            ids,
        ))
    }

    pub(crate) fn default_unquantified_effects(&mut self, retained: &FxHashSet<EffectVar>) {
        let mut variables = FxHashSet::default();
        for node in &self.nodes {
            node.constraint.fill_with_inner_effect_vars(&mut variables);
            if let EvidencePlanSource::Selected { application, .. } = &node.source {
                for ty in application.substitution.0.values() {
                    ty.fill_with_inner_effect_vars(&mut variables);
                }
                for effect in application.substitution.1.values() {
                    effect.fill_with_inner_effect_vars(&mut variables);
                }
            }
        }
        for field_use in &self.field_uses {
            field_use
                .required
                .fill_with_inner_effect_vars(&mut variables);
            for ty in &field_use.ty_args {
                ty.fill_with_inner_effect_vars(&mut variables);
            }
            for effect in &field_use.eff_args {
                effect.fill_with_inner_effect_vars(&mut variables);
            }
        }
        let effects = variables
            .into_iter()
            .filter(|var| !retained.contains(var))
            .map(|var| (var, EffType::empty()))
            .collect::<FxHashMap<_, _>>();
        if !effects.is_empty() {
            self.instantiate_in_place(&mut BitmapInstantiationMapper::new(&(
                FxHashMap::default(),
                effects,
            )));
        }
    }

    pub(crate) fn instantiate_in_place(&mut self, mapper: &mut impl TypeMapper) {
        for node in &mut self.nodes {
            node.constraint = node.constraint.map(mapper);
            if let EvidencePlanSource::Selected { application, .. } = &mut node.source {
                for ty in application.substitution.0.values_mut() {
                    *ty = ty.map(mapper);
                }
                for eff in application.substitution.1.values_mut() {
                    *eff = mapper.map_effect_type(eff);
                }
            }
        }
        for field_use in &mut self.field_uses {
            field_use.required = field_use.required.map(mapper);
            for ty in &mut field_use.ty_args {
                *ty = ty.map(mapper);
            }
            for eff in &mut field_use.eff_args {
                *eff = mapper.map_effect_type(eff);
            }
        }
    }

    pub(crate) fn substitute(&mut self, inference: &mut UnifiedTypeInference) {
        for node in &mut self.nodes {
            node.constraint = inference.substitute_in_constraint(&node.constraint);
            if let EvidencePlanSource::Selected { application, .. } = &mut node.source {
                for ty in application.substitution.0.values_mut() {
                    *ty = inference.substitute_in_type(*ty);
                }
                for eff in application.substitution.1.values_mut() {
                    *eff = inference.substitute_in_effect_type(eff);
                }
            }
        }
        for field_use in &mut self.field_uses {
            inference.substitute_in_subscript_type_in_place(&mut field_use.required);
            inference.substitute_in_types_in_place(&mut field_use.ty_args);
            inference.substitute_in_effect_types_in_place(&mut field_use.eff_args);
        }
    }

    /// Replace the reduction that the plan holds with `reduced`, keeping the uses of declared
    /// fields, which are of the inference of the function and not of a reduction.
    pub(crate) fn replace_reduction(&mut self, reduced: Self) {
        let field_uses = mem::take(&mut self.field_uses);
        *self = reduced;
        self.field_uses = field_uses;
    }

    /// Take the uses of declared fields that `inference` made, as it has them now.
    pub(crate) fn record_field_uses(&mut self, inference: &UnifiedTypeInference) {
        self.field_uses = inference.field_uses().to_vec();
    }
}

pub(crate) struct ReducedRequirements {
    pub(crate) requirements: Vec<PubTypeConstraint>,
    pub(crate) evidence: EvidencePlan,
}

/// Exact artifact identity, including fixed output bounds. Unlike requirement lookup, this
/// must not equate distinct method contracts. Substitutions are stored in source-variable order.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct UniformDictionaryKey {
    source: TraitImplId,
    types: Vec<(TypeVar, Type)>,
    effects: Vec<(EffectVar, EffType)>,
    trait_id: TraitId,
    inputs: Vec<Type>,
    outputs: Vec<Type>,
    output_effects: Vec<EffType>,
    recursive_plan: Option<Box<EvidencePlan>>,
}

struct SourceCandidate {
    id: TraitImplId,
    inputs: Vec<Type>,
    outputs: Vec<Type>,
    effects: Vec<EffType>,
    type_count: u32,
    effect_count: u32,
    constraints: Vec<PubTypeConstraint>,
}

struct UniformApplication {
    dictionary: TraitImplId,
    substitution: InstSubst,
    obligations: Vec<PubTypeConstraint>,
    capture_obligations: Vec<usize>,
    type_count: u32,
    effect_count: u32,
}

enum UniformSelection {
    Selected(UniformApplication),
    Absent,
    Deferred,
}

fn is_closed_trait_requirement(constraint: &PubTypeConstraint) -> bool {
    matches!(constraint, PubTypeConstraint::HaveTrait { input_tys, output_tys, output_effs, .. }
        if input_tys.iter().chain(output_tys).all(TypeLike::is_constant)
            && output_effs.iter().all(|effect| !effect.has_variables()))
}

fn unresolved(constraint: &PubTypeConstraint) -> InternalCompilationError {
    internal_compilation_error!(PrivateRequirementInPublicContract {
        requirement: constraint.clone(),
        type_names: FxHashMap::default(),
        span: constraint.use_site(),
    })
}

/// Independent quantifiers belong to the caller, including those occurring only in a result.
/// Only trait outputs reachable from protected variables or concrete inputs may be determined
/// by reduction. An unanchored cycle of output dependencies does not establish determination.
fn reduction_rigid_types(
    constraints: &[PubTypeConstraint],
    protected: &[Type],
    inference: &mut UnifiedTypeInference,
) -> Vec<Type> {
    let constraints = constraints
        .iter()
        .map(|constraint| inference.substitute_in_constraint(constraint))
        .collect::<Vec<_>>();
    let mut rigid = collect_ty_vars(&inference.substitute_in_types(protected))
        .into_iter()
        .collect::<FxHashSet<_>>();
    let variables = constraints.inner_ty_vars();
    let dependencies = constraints
        .iter()
        .filter_map(|constraint| match constraint {
            PubTypeConstraint::HaveTrait {
                input_tys,
                output_tys,
                ..
            } => Some((collect_ty_vars(input_tys), collect_ty_vars(output_tys))),
            _ => None,
        })
        .collect::<Vec<_>>();
    let outputs = dependencies
        .iter()
        .flat_map(|(_, outputs)| outputs.iter().copied())
        .collect::<FxHashSet<_>>();
    rigid.extend(
        variables
            .iter()
            .filter(|var| !outputs.contains(var))
            .copied(),
    );
    let mut determined = rigid.clone();
    loop {
        let count = determined.len();
        for (inputs, outputs) in &dependencies {
            if inputs.iter().all(|var| determined.contains(var)) {
                determined.extend(outputs.iter().copied());
            }
        }
        if determined.len() == count {
            break;
        }
    }
    rigid.extend(
        variables
            .into_iter()
            .filter(|var| !determined.contains(var)),
    );
    rigid.into_iter().sorted().map(Type::variable).collect()
}

impl TraitSolver<'_> {
    /// Preserve the instantiation at the call into each source entry. Passing a source blanket
    /// dictionary directly loses it, in particular when a native entry's parameter is replaced
    /// by a structured type. The thunks use the existing dictionary capture convention.
    pub(crate) fn materialize_uniform_dictionary(
        &mut self,
        application: &SelectedEvidence,
        requirement: &DictionaryReq,
        span: Location,
    ) -> Result<TraitImplId, InternalCompilationError> {
        let DictionaryReq::TraitImpl {
            trait_id,
            input_tys,
            output_tys,
            output_effs,
        } = requirement
        else {
            unreachable!()
        };
        let key = UniformDictionaryKey {
            source: application.dictionary,
            types: application
                .substitution
                .0
                .iter()
                .map(|(v, t)| (*v, *t))
                .sorted_by_key(|(v, _)| *v)
                .collect(),
            effects: application
                .substitution
                .1
                .iter()
                .map(|(v, e)| (*v, e.clone()))
                .sorted_by_key(|(v, _)| *v)
                .collect(),
            trait_id: *trait_id,
            inputs: input_tys.clone(),
            outputs: output_tys.clone(),
            output_effects: output_effs.clone(),
            recursive_plan: None,
        };
        if let Some(id) = self.impls.uniform_dictionaries.get(&key) {
            return Ok(TraitImplId::new(self.current_type_items.module.id, *id));
        }
        let source = self.get_impl_data_by_id(application.dictionary).clone();
        let mut mapper = BitmapInstantiationMapper::new(&application.substitution);
        let captures = source
            .dictionary_value
            .capture_schema()
            .iter()
            .map(|req| req.instantiate(&mut mapper))
            .collect::<Vec<_>>();
        let trait_def = self.trait_def(*trait_id);
        let mut definitions = trait_def.instantiate_for_tys(input_tys, output_tys, output_effs);
        for ty in
            trait_def.instantiate_associated_const_tys_for_tys(input_tys, output_tys, output_effs)
        {
            definitions.push(CallableDefinition::new(
                TypeScheme::new_infer_quantifiers(FnType::new_by_val([], ty, EffType::empty())),
                vec![],
                None,
            ));
        }
        let mut entries = Vec::new();
        let mut mappings = Vec::new();
        for (index, (function, definition)) in source
            .methods
            .iter()
            .chain(&source.associated_const_getters)
            .zip(definitions)
            .enumerate()
        {
            let index = TraitDictionaryEntryIndex::from_index(index);
            let callee = source
                .dictionary_value
                .project_entry_captures(index, &captures, || requirement.clone())
                .expect("source dictionary has valid entry captures");
            // Two requirements of the source can be one at these types, and one can need no
            // evidence any more. The entry takes each once, in the order of its first use,
            // and gives it to every argument of the method that asks for it.
            let entry = DictionaryEntryRequirements::canonical(&callee, |id| self.trait_def(id));
            let source_mapping = source.dictionary_value.entry_capture_mapping(index);
            let mapping = entry
                .as_slice()
                .iter()
                .map(|requirement| {
                    let argument = callee
                        .iter()
                        .position(|asked| asked == requirement)
                        .expect("an entry requirement is one of the method");
                    source_mapping[argument]
                })
                .collect::<Vec<_>>();
            let requirements = BlanketMethodRequirements { entry, callee };
            let mut function = self.materialize_blanket_method_thunk(
                *function,
                Some(application.dictionary.module),
                &definition,
                application.type_count,
                application.effect_count,
                &application.substitution,
                &requirements,
                span,
            )?;
            let mut scheme = function.definition.ty_scheme.clone();
            let normalization = scheme.normalize();
            instantiate_function_descr_in_place(
                &mut function,
                &mut BitmapInstantiationMapper::new(&normalization),
            );
            function.definition.ty_scheme = scheme;
            let id = self.fn_collector.next_id();
            let name = Ustr::from(&format!("__uniform_dictionary_{}", id.as_index()));
            self.fn_collector
                .push_with_visibility(name, function, Visibility::Module);
            entries.push(id);
            mappings.push(mapping);
        }
        let mut getters = entries.split_off(source.methods.len());
        let mut associated_const_values = source.associated_const_values;
        if getters.is_empty() && self.trait_def(*trait_id).associated_const_count() != 0 {
            // Compiler-provided blankets may leave fixed layout constants to materialization.
            // Source impls already have their complete, provider-owned getter dictionaries.
            associated_const_values = materialized_associated_const_values(
                *trait_id,
                self.trait_def(*trait_id),
                input_tys,
                &associated_const_values,
                span,
                self,
            )?;
            let tys = self
                .trait_def(*trait_id)
                .instantiate_associated_const_tys_for_tys(input_tys, output_tys, output_effs);
            getters = TraitImpls::bundle_pending_trivial_associated_const_getters(
                &associated_const_values,
                &tys,
                &mut self.fn_collector,
                |index| Ustr::from(&format!("__uniform_dictionary_constant_{index}")),
            );
            mappings.extend(getters.iter().map(|_| Vec::new()));
        }

        let dictionary = build_capturing_dictionary_value(&entries, &getters, captures, mappings);
        let ty = self.trait_def(*trait_id).get_dictionary_type_for_tys(
            input_tys,
            output_tys,
            output_effs,
        );
        let imp = TraitImpl::new(
            *trait_id,
            output_tys.clone(),
            output_effs.clone(),
            entries,
            dictionary,
            ty,
            false,
            None,
        )
        .with_associated_const_values(associated_const_values)
        .with_associated_const_getters(getters);
        let id = self.impls.add_anonymous_dictionary_struct(imp);
        self.record_generated_source(
            id,
            (application.dictionary.module != self.current_type_items.module.id)
                .then_some(application.dictionary.module),
            application.dictionary.impl_id,
        );
        Rc::make_mut(&mut self.impls.uniform_dictionaries).insert(key, id);
        Ok(TraitImplId::new(self.current_type_items.module.id, id))
    }

    /// Adapt generated entries to construct their private members from self evidence at call
    /// time. The generated implementation remains unchanged; methods and layout getters use
    /// the same thunk and SelfDictionary machinery as ordinary dictionary entries.
    pub(crate) fn materialize_recursive_value_dictionary(
        &mut self,
        requirement: &DictionaryReq,
        entry_plan: &EvidencePlan,
        span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImplId, InternalCompilationError> {
        let DictionaryReq::TraitImpl {
            trait_id,
            input_tys,
            ..
        } = requirement
        else {
            unreachable!()
        };
        let (canonical, substitution) = alpha_canonicalize_types_with_instantiation(input_tys);
        let (source_id, _) = self
            .materialize_compiler_provided_value_dictionary(arena, *trait_id, &canonical, span)?;
        let key = UniformDictionaryKey {
            source: source_id,
            types: substitution
                .0
                .iter()
                .map(|(v, t)| (*v, *t))
                .sorted_by_key(|(v, _)| *v)
                .collect(),
            effects: substitution
                .1
                .iter()
                .map(|(v, e)| (*v, e.clone()))
                .sorted_by_key(|(v, _)| *v)
                .collect(),
            trait_id: *trait_id,
            inputs: input_tys.clone(),
            outputs: vec![],
            output_effects: vec![],
            recursive_plan: Some(Box::new(entry_plan.clone())),
        };
        if let Some(id) = self.impls.uniform_dictionaries.get(&key) {
            return Ok(TraitImplId::new(self.current_type_items.module.id, *id));
        }
        let source = self.get_impl_data_by_id(source_id).clone();
        let mut mapper = BitmapInstantiationMapper::new(&substitution);
        let captures = source
            .dictionary_value
            .capture_schema()
            .iter()
            .map(|req| req.instantiate(&mut mapper))
            .collect::<Vec<_>>();
        let mut supplied = entry_plan
            .nodes
            .iter()
            .filter(|node| matches!(node.source, EvidencePlanSource::Public))
            .filter_map(|node| node.constraint.dictionary_requirement_key(*trait_id))
            .collect::<Vec<_>>();
        supplied.push(requirement.clone());
        let entry = DictionaryEntryRequirements::canonical(&supplied, |id| self.trait_def(id));
        let trait_def = self.trait_def(*trait_id);
        let mut definitions = trait_def.instantiate_for_tys(input_tys, &[], &[]);
        for ty in trait_def.instantiate_associated_const_tys_for_tys(input_tys, &[], &[]) {
            definitions.push(CallableDefinition::new(
                TypeScheme::new_infer_quantifiers(FnType::new_by_val([], ty, EffType::empty())),
                vec![],
                None,
            ));
        }
        let mut canonical_definitions =
            self.trait_def(*trait_id)
                .instantiate_for_tys(&canonical, &[], &[]);
        canonical_definitions.extend(definitions.iter().skip(source.methods.len()).cloned());
        let mut entries = Vec::new();
        for (index, (function, definition)) in source
            .methods
            .iter()
            .chain(&source.associated_const_getters)
            .zip(definitions)
            .enumerate()
        {
            let callee = source
                .dictionary_value
                .project_entry_captures(
                    TraitDictionaryEntryIndex::from_index(index),
                    &captures,
                    || requirement.clone(),
                )
                .expect("generated dictionary has valid entry captures");
            // Generated getters quantify only variables used by their formula, unlike blanket
            // methods (which quantify the whole impl). Derive this generated entry's scheme
            // from its canonical signature and exact evidence ABI, using the generator's rule.
            let canonical_callee = source
                .dictionary_value
                .project_entry_captures(
                    TraitDictionaryEntryIndex::from_index(index),
                    source.dictionary_value.capture_schema(),
                    || DictionaryReq::new_trait_impl(*trait_id, canonical.clone(), vec![], vec![]),
                )
                .expect("generated dictionary has valid entry captures");
            let source_definition = Self::dictionary_entry_definition(
                &canonical_definitions[index],
                &canonical_callee,
                span,
            );
            let source_scheme = &source_definition.ty_scheme;
            let inst_data = FnInstData::new(
                callee,
                source_scheme
                    .ty_quantifiers
                    .iter()
                    .map(|var| substitution.0[var])
                    .collect(),
                source_scheme
                    .eff_quantifiers
                    .iter()
                    .map(|var| substitution.1[var].clone())
                    .collect(),
            );
            let function_id = self.function_id(source_id.module, *function);
            let (body, locals) = self.blanket_method_thunk_code_entry(
                function_id,
                &definition,
                &[],
                inst_data,
                span,
            )?;
            let mut function = PendingModuleFunction::from_body(
                Self::dictionary_entry_definition(&definition, entry.as_slice(), span),
                body,
                definition.arg_names.len(),
                None,
                locals,
            );
            function.evidence_plan = entry_plan.clone();
            let mut scheme = function.definition.ty_scheme.clone();
            let normalization = scheme.normalize();
            instantiate_function_descr_in_place(
                &mut function,
                &mut BitmapInstantiationMapper::new(&normalization),
            );
            function.definition.ty_scheme = scheme;
            let id = self.fn_collector.next_id();
            self.fn_collector.push_with_visibility(
                Ustr::from(&format!("__recursive_value_{}", id.as_index())),
                function,
                Visibility::Module,
            );
            entries.push(id);
        }
        let entry_requirements = vec![entry; entries.len()];
        let (captures, mappings) =
            dictionary_capture_plan(*trait_id, input_tys, &entry_requirements);
        let getters = entries.split_off(source.methods.len());
        let dictionary = build_capturing_dictionary_value(&entries, &getters, captures, mappings);
        let ty = self
            .trait_def(*trait_id)
            .get_dictionary_type_for_tys(input_tys, &[], &[]);
        let implementation = TraitImpl::new(
            *trait_id,
            vec![],
            vec![],
            entries,
            dictionary,
            ty,
            false,
            None,
        )
        .with_associated_const_values(source.associated_const_values)
        .with_associated_const_getters(getters);
        let id = self.impls.add_anonymous_dictionary_struct(implementation);
        Rc::make_mut(&mut self.impls.uniform_dictionaries).insert(key, id);
        Ok(TraitImplId::new(self.current_type_items.module.id, id))
    }

    fn definition_is_public(&self, module: ModuleId, kind: DefKind) -> bool {
        let table = if module == self.current_type_items.module.id {
            self.current_def_table
        } else {
            let Some(module) = self.others.get(module).and_then(|entry| entry.module()) else {
                return false;
            };
            &module.def_table
        };
        let name = match kind {
            DefKind::Trait(index) => self.trait_def(TraitId::new(module, index)).name,
            DefKind::TypeDef(index) => self.type_def(TypeDefId::new(module, index)).name,
            _ => unreachable!("only types and traits appear in requirements"),
        };
        table
            .get_by_name(&name)
            .is_some_and(|(_, def)| def.visibility.is_public())
    }

    pub(crate) fn requirement_is_public(&self, constraint: &PubTypeConstraint) -> bool {
        if let PubTypeConstraint::HaveTrait { trait_id, .. } = constraint
            && !self.definition_is_public(trait_id.module, DefKind::Trait(trait_id.index))
        {
            return false;
        }
        struct Check<'a, 'b> {
            solver: &'a TraitSolver<'b>,
            public: bool,
        }
        impl TypeInnerVisitor for Check<'_, '_> {
            fn visit_ty_kind_start(&mut self, ty: &TypeKind) {
                if let TypeKind::Named(named) = ty {
                    self.public &= self
                        .solver
                        .definition_is_public(named.def.module, DefKind::TypeDef(named.def.index));
                }
            }
        }
        let mut check = Check {
            solver: self,
            public: true,
        };
        constraint.visit(&mut check);
        check.public
    }

    fn reduction_candidates(&self, trait_id: TraitId, inputs: &[Type]) -> Vec<SourceCandidate> {
        let mut candidates = Vec::new();
        let mut collect = |module: ModuleId, impls: &TraitImpls, local: bool| {
            for (key, id) in impls.concrete() {
                let imp = impls.get_impl_by_local_id(*id);
                if key.trait_id != trait_id
                    || (!local && !self.can_use_other_impl(module, imp))
                    || (!imp.public && imp.source_span.is_none())
                    || !input_heads_may_match(&key.input_tys, inputs)
                {
                    continue;
                }
                candidates.push(SourceCandidate {
                    id: TraitImplId::new(module, *id),
                    inputs: key.input_tys.clone(),
                    outputs: imp.output_tys.clone(),
                    effects: imp.output_effs.clone(),
                    type_count: 0,
                    effect_count: 0,
                    constraints: Vec::new(),
                });
            }
            if let Some(blankets) = impls.blanket().get(&trait_id) {
                for (key, id) in blankets {
                    let imp = impls.get_impl_by_local_id(*id);
                    if (!local && !self.can_use_other_impl(module, imp))
                        || !input_heads_may_match(&key.input_tys, inputs)
                    {
                        continue;
                    }
                    candidates.push(SourceCandidate {
                        id: TraitImplId::new(module, *id),
                        inputs: key.input_tys.clone(),
                        outputs: imp.output_tys.clone(),
                        effects: imp.output_effs.clone(),
                        type_count: key.ty_var_count,
                        effect_count: key.eff_var_count,
                        constraints: key.constraints.clone(),
                    });
                }
            }
        };
        collect(self.current_type_items.module.id, self.impls, true);
        for (_, module) in
            named_modules_in_environment(self.others, self.current_type_items.environment)
        {
            collect(module.module_id(), &module.impls, false);
        }
        candidates
    }

    /// Select a source dictionary uniformly, without specializing `rigid_inputs`. A possible
    /// specialization is not absence and must also prevent falling back to a derivation.
    fn select_uniform_application(
        &mut self,
        constraint: &PubTypeConstraint,
        rigid_inputs: &[Type],
        inference: &mut UnifiedTypeInference,
    ) -> Result<UniformSelection, InternalCompilationError> {
        let PubTypeConstraint::HaveTrait {
            trait_id,
            input_tys,
            output_tys,
            output_effs,
            ..
        } = constraint
        else {
            return Err(unresolved(constraint));
        };
        let span = constraint.use_site();
        let inputs = inference.substitute_in_types(input_tys);
        if self.impls.pending.blocks(*trait_id, &inputs) {
            return Err(unresolved(constraint));
        }
        let rigid = collect_ty_vars(&inference.substitute_in_types(rigid_inputs))
            .into_iter()
            .map(Type::variable)
            .collect::<Vec<_>>();
        let head_rigid = rigid
            .iter()
            .copied()
            .chain(collect_ty_vars(&inputs).into_iter().map(Type::variable))
            .unique()
            .collect::<Vec<_>>();
        let mut selected = None;
        for candidate in self.reduction_candidates(*trait_id, &inputs) {
            let snapshot = inference.snapshot();
            let mut probe = TraitSolverProbe::from_solver(self);
            let structural_candidate = TraitImprovementCandidate::Blanket {
                input_tys: candidate.inputs.clone(),
                output_tys: candidate.outputs.clone(),
                output_effs: candidate.effects.clone(),
                ty_var_count: candidate.type_count,
                eff_var_count: candidate.effect_count,
                constraints: candidate.constraints.clone(),
            };
            // Only the head must fit without specializing an enclosing input. A public
            // prerequisite such as `[T]: Read` remains a condition on callers, even if its
            // currently visible impls would narrow T. Private prerequisites are reduced below
            // and undergo this same head check themselves.
            let erased_inputs = instantiate_types(&candidate.inputs, &mut EffectErasingMapper);
            let erased_query = instantiate_types(&inputs, &mut EffectErasingMapper);
            let head_substitution = (
                inference.fresh_type_var_subst(candidate.type_count),
                inference.fresh_effect_var_subst(candidate.effect_count),
            );
            let uniform = erased_inputs
                .iter()
                .zip(&erased_query)
                .all(|(head, input)| {
                    inference
                        .unify_same_type_with_sub_effects(
                            head.instantiate_simple(&head_substitution),
                            span,
                            *input,
                            span,
                        )
                        .is_ok()
                })
                // Selection matches a head against the query; it must not improve the query's
                // inputs, including fresh outputs supplied by a public prerequisite.
                && inference.declared_generics_intact(&head_rigid);
            inference.rollback_to(snapshot);
            let snapshot = inference.snapshot();
            let possible = Self::improvement_candidate_applies_by_structure(
                &mut probe,
                inference,
                &structural_candidate,
                &inputs,
                None,
                ConstraintAssumptions::all(&[]),
                span,
                &mut NodeArena::default(),
            );
            inference.rollback_to(snapshot);
            let possible = possible?;
            if possible {
                if !uniform || selected.is_some() {
                    return Ok(UniformSelection::Deferred);
                }
                selected = Some(candidate);
            }
        }
        let Some(candidate) = selected else {
            return Ok(UniformSelection::Absent);
        };
        // Match capture slots to the selected impl's own declared prerequisites, before any
        // instantiation. Keep the complete contract, including fixed effect bounds, and record
        // these indices immediately when allocating that impl's obligation nodes.
        let value_trait = self.std_trait_id(VALUE_TRAIT_NAME);
        let capture_obligations = self
            .get_impl_data_by_id(candidate.id)
            .dictionary_value
            .capture_schema()
            .iter()
            .map(|capture| {
                candidate
                    .constraints
                    .iter()
                    .position(|constraint| {
                        constraint
                            .dictionary_requirement_key(value_trait)
                            .is_some_and(|requirement| requirement.same_contract(capture))
                    })
                    .ok_or_else(|| {
                        internal_compilation_error!(Internal {
                            error: "A source dictionary capture has no corresponding prerequisite"
                                .into(),
                            span,
                        })
                    })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let mut substitution = (
            inference.fresh_type_var_subst(candidate.type_count),
            inference.fresh_effect_var_subst(candidate.effect_count),
        );
        for (head, input) in candidate.inputs.iter().zip(&inputs) {
            inference.unify_same_type_with_sub_effects(
                head.instantiate_simple(&substitution),
                span,
                *input,
                span,
            )?;
        }
        for (head, output) in candidate.outputs.iter().zip(output_tys) {
            inference.unify_same_type_with_sub_effects(
                head.instantiate_simple(&substitution),
                span,
                *output,
                span,
            )?;
        }
        for (index, ((head, output), polarity)) in candidate
            .effects
            .iter()
            .zip(output_effs)
            .zip(self.output_effect_polarities(*trait_id))
            .enumerate()
        {
            let head = head.instantiate(&substitution.1);
            let origin = self.output_effect_origin(*trait_id, index, span);
            inference.relate_trait_output_effect(&head, output, polarity, span, origin)?;
        }
        if !inference.declared_generics_intact(&rigid) {
            return Err(unresolved(constraint));
        }
        for ty in substitution.0.values_mut() {
            *ty = inference.substitute_in_type(*ty);
        }
        for eff in substitution.1.values_mut() {
            *eff = inference.substitute_in_effect_type(eff);
        }
        let obligations = candidate
            .constraints
            .iter()
            .map(|c| {
                let mut obligation = c
                    .instantiate_simple(&substitution)
                    .instantiate_location_cloned(span);
                obligation.set_origin(constraint.origin());
                obligation
            })
            .collect();
        Ok(UniformSelection::Selected(UniformApplication {
            dictionary: candidate.id,
            substitution,
            obligations,
            capture_obligations,
            type_count: candidate.type_count,
            effect_count: candidate.effect_count,
        }))
    }

    /// Replace private requirements by public evidence leaves. Substitutions stay in the item's
    /// inference context, including output-only variables determined by the private evidence.
    pub(crate) fn reduce_public_requirements(
        &mut self,
        constraints: Vec<PubTypeConstraint>,
        rigid_inputs: &[Type],
        inference: &mut UnifiedTypeInference,
        arena: &mut NodeArena,
    ) -> Result<ReducedRequirements, InternalCompilationError> {
        // Reduction introduces more obligations. Reading a fresh variable through its published
        // ceiling here would turn an upper bound into an equality before those obligations meet.
        let finalized = inference.effects_finalized();
        inference.restore_effects_finalized(false);
        let result = self.reduce_public_requirements_in_inference(
            constraints,
            rigid_inputs,
            inference,
            arena,
        );
        inference.restore_effects_finalized(finalized);
        result
    }

    fn reduce_public_requirements_in_inference(
        &mut self,
        constraints: Vec<PubTypeConstraint>,
        rigid_inputs: &[Type],
        inference: &mut UnifiedTypeInference,
        arena: &mut NodeArena,
    ) -> Result<ReducedRequirements, InternalCompilationError> {
        if constraints.iter().all(|c| self.requirement_is_public(c)) {
            return Ok(ReducedRequirements {
                requirements: constraints,
                evidence: EvidencePlan::default(),
            });
        }
        let original = constraints
            .iter()
            .find(|c| !self.requirement_is_public(c))
            .unwrap()
            .clone();
        let rigid = reduction_rigid_types(&constraints, rigid_inputs, inference);
        let mut evidence = EvidencePlan::default();
        for constraint in constraints {
            let root = evidence.push(constraint, None);
            evidence.roots.push(root);
        }
        let mut work = REDUCTION_WORK_LIMIT;
        let mut pending = evidence.roots.iter().rev().copied().collect::<Vec<_>>();
        loop {
            let mut deferred = Vec::new();
            let mut progress = false;
            while let Some(id) = pending.pop() {
                let start = evidence.nodes.len();
                if self.reduce_evidence_node(
                    id,
                    &rigid,
                    inference,
                    arena,
                    &mut work,
                    &mut evidence,
                )? {
                    progress = true;
                    pending.extend((start..evidence.nodes.len()).rev());
                } else {
                    deferred.push(id);
                }
            }
            let mut leaves = evidence
                .nodes
                .iter()
                .filter(|node| matches!(node.source, EvidencePlanSource::Public))
                .map(|node| inference.substitute_in_constraint(&node.constraint))
                .collect::<Vec<_>>();
            inference.coalesce_constraint_outputs(&mut leaves, &|id| {
                self.output_effect_polarities(id)
            })?;
            if !inference.declared_generics_intact(&rigid) {
                return Err(unresolved(&original));
            }
            evidence.substitute(inference);
            // An output equality may expose a private type in a formerly public leaf. Reduce
            // that same node: incoming edges keep their identity, without a graph-wide redirect.
            for (id, node) in evidence.nodes.iter_mut().enumerate() {
                if matches!(node.source, EvidencePlanSource::Public)
                    && (!self.requirement_is_public(&node.constraint)
                        || is_closed_trait_requirement(&node.constraint))
                {
                    node.source = EvidencePlanSource::Pending;
                    deferred.push(id);
                    progress = true;
                }
            }
            if deferred.is_empty() {
                evidence.check_construction_cycles()?;
                return Ok(ReducedRequirements {
                    requirements: leaves,
                    evidence,
                });
            }
            if !progress {
                return Err(unresolved(&evidence.nodes[deferred[0]].constraint));
            }
            deferred.reverse();
            pending = deferred;
        }
    }

    /// Expand one node, preserving its identity. A query whose inputs another private output
    /// may determine is postponed; a full round without progress reports an ordinary rejection.
    #[allow(clippy::too_many_arguments)]
    fn reduce_evidence_node(
        &mut self,
        id: usize,
        rigid_inputs: &[Type],
        inference: &mut UnifiedTypeInference,
        arena: &mut NodeArena,
        work: &mut usize,
        evidence: &mut EvidencePlan,
    ) -> Result<bool, InternalCompilationError> {
        let mut constraint = inference.substitute_in_constraint(&evidence.nodes[id].constraint);
        if self.requirement_is_public(&constraint) {
            evidence.nodes[id].constraint = constraint.clone();
            evidence.nodes[id].source = if is_closed_trait_requirement(&constraint) {
                let PubTypeConstraint::HaveTrait {
                    trait_id,
                    input_tys,
                    output_tys,
                    output_effs,
                    ..
                } = &constraint
                else {
                    unreachable!()
                };
                EvidencePlanSource::Ground(self.solve_impl_for_application(
                    *trait_id,
                    input_tys,
                    output_tys,
                    output_effs,
                    &FxHashSet::default(),
                    constraint.use_site(),
                    arena,
                )?)
            } else {
                EvidencePlanSource::Public
            };
            return Ok(true);
        }
        if let PubTypeConstraint::VariantPayloadLayout { payload_ty, .. } = &constraint {
            let mut value = PubTypeConstraint::new_have_trait(
                self.std_trait_id(VALUE_TRAIT_NAME),
                vec![*payload_ty],
                vec![],
                vec![],
                constraint.use_site(),
            );
            value.set_origin(constraint.origin());
            constraint = value;
        }
        evidence.nodes[id].constraint = constraint.clone();
        if *work == 0 {
            return Err(unresolved(&constraint));
        }
        let mut ancestor = evidence.nodes[id].parent;
        let mut crosses_generated_value = false;
        while let Some(parent) = ancestor {
            let generated = matches!(
                evidence.nodes[parent].source,
                EvidencePlanSource::GeneratedValue { .. }
            );
            if inference.substitute_in_constraint(&evidence.nodes[parent].constraint) == constraint
            {
                if generated {
                    evidence.nodes[id].source =
                        EvidencePlanSource::SelfReference { target: parent };
                    return Ok(true);
                }
                // A custom Value may be the first node encountered in the cycle. Expand it
                // once inside the generated entry, until its generated ancestor becomes self.
                if !crosses_generated_value
                    || !matches!(&constraint,
                    PubTypeConstraint::HaveTrait { trait_id, .. } if *trait_id == self.std_trait_id(VALUE_TRAIT_NAME))
                {
                    return Err(unresolved(&constraint));
                }
                break;
            }
            crosses_generated_value |= generated;
            ancestor = evidence.nodes[parent].parent;
        }
        let PubTypeConstraint::HaveTrait {
            trait_id,
            input_tys,
            output_tys,
            output_effs,
            ..
        } = &constraint
        else {
            return Err(unresolved(&constraint));
        };
        if *trait_id == self.std_trait_id(VALUE_TRAIT_NAME)
            && input_tys.len() == 1
            && let Some(types) = generated_value_evidence_types(input_tys[0], self)
        {
            if self.impls.pending.blocks(*trait_id, input_tys) {
                return Err(unresolved(&constraint));
            }
            let mut members = Vec::new();
            for ty in types {
                if ty == input_tys[0] {
                    members.push(id);
                    continue;
                }
                let mut member = PubTypeConstraint::new_have_trait(
                    *trait_id,
                    vec![ty],
                    vec![],
                    vec![],
                    constraint.use_site(),
                );
                member.set_origin(constraint.origin());
                members.push(evidence.push(member, Some(id)));
            }
            evidence.nodes[id].source = EvidencePlanSource::GeneratedValue { members };
            *work -= 1;
            return Ok(true);
        }
        match self.select_uniform_application(&constraint, rigid_inputs, inference)? {
            UniformSelection::Selected(application) => {
                let children = application
                    .obligations
                    .into_iter()
                    .map(|obligation| evidence.push(obligation, Some(id)))
                    .collect::<Vec<_>>();
                let captures = application
                    .capture_obligations
                    .into_iter()
                    .map(|index| children[index])
                    .collect();
                evidence.nodes[id].source = EvidencePlanSource::Selected {
                    application: SelectedEvidence {
                        dictionary: application.dictionary,
                        substitution: application.substitution,
                        type_count: application.type_count,
                        effect_count: application.effect_count,
                    },
                    captures,
                };
                *work -= 1;
                Ok(true)
            }
            UniformSelection::Absent if input_tys.iter().all(TypeLike::is_constant) => {
                let selected = self.solve_impl_for_application(
                    *trait_id,
                    input_tys,
                    output_tys,
                    output_effs,
                    &constraint.inner_effect_vars(),
                    constraint.use_site(),
                    arena,
                )?;
                let implementation = self.get_impl_data_by_id(selected);
                for (actual, expected) in implementation.output_tys.iter().zip(output_tys) {
                    inference.unify_same_type_with_sub_effects(
                        *actual,
                        constraint.use_site(),
                        *expected,
                        constraint.use_site(),
                    )?;
                }
                for (actual, expected) in implementation.output_effs.iter().zip(output_effs) {
                    inference.unify_same_effect(
                        actual,
                        constraint.use_site(),
                        expected,
                        constraint.use_site(),
                    )?;
                }
                evidence.nodes[id].source = EvidencePlanSource::Ground(selected);
                *work -= 1;
                Ok(true)
            }
            UniformSelection::Absent | UniformSelection::Deferred => Ok(false),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        Modules,
        module::{LocalImplId, LocalTraitId, Module},
        types::trait_solver::trait_solver_from_module,
    };

    fn dependency(input: Type, output: Type) -> PubTypeConstraint {
        PubTypeConstraint::new_have_trait(
            TraitId::new(ModuleId::new(0), LocalTraitId::new(0)),
            vec![input],
            vec![output],
            vec![],
            Location::new_synthesized(),
        )
    }

    #[test]
    fn evidence_artifacts_follow_module_and_solver_rollback() {
        use crate::Path;
        let module_id = ModuleId::new(0);
        let mut module = Module::new(module_id, Path::single_str("$evidence_rollback"));
        let checkpoint = module.checkpoint(&[]);
        let key = UniformDictionaryKey {
            source: TraitImplId::new(module_id, LocalImplId::new(0)),
            types: vec![],
            effects: vec![],
            trait_id: TraitId::new(module_id, LocalTraitId::new(0)),
            inputs: vec![Type::unit()],
            outputs: vec![],
            output_effects: vec![],
            recursive_plan: None,
        };
        Rc::make_mut(&mut module.impls.uniform_dictionaries)
            .insert(key.clone(), LocalImplId::new(0));
        let modules = Modules::default();
        {
            let mut solver = trait_solver_from_module!(module, &modules);
            let snapshot = solver.snapshot_derived_impl_state();
            let mut other = key.clone();
            other.inputs = vec![Type::never()];
            Rc::make_mut(&mut solver.impls.uniform_dictionaries)
                .insert(other.clone(), LocalImplId::new(1));
            solver.rollback_derived_impl_state(snapshot);
            assert!(solver.impls.uniform_dictionaries.contains_key(&key));
            assert!(!solver.impls.uniform_dictionaries.contains_key(&other));
        }
        module.restore(checkpoint);
        assert!(module.impls.uniform_dictionaries.is_empty());
    }

    #[test]
    fn output_dependency_chains_preserve_only_their_independent_root() {
        let vars = [
            Type::variable_id(0),
            Type::variable_id(1),
            Type::variable_id(2),
        ];
        let constraints = [dependency(vars[1], vars[2]), dependency(vars[0], vars[1])];
        let mut inference = UnifiedTypeInference::new_with_ty_vars(3);
        assert_eq!(
            reduction_rigid_types(&constraints, &[], &mut inference),
            vec![vars[0]]
        );
        assert_eq!(
            reduction_rigid_types(&constraints, &[vars[2]], &mut inference),
            vec![vars[0], vars[2]],
        );
    }

    #[test]
    fn an_unanchored_output_cycle_does_not_determine_its_own_variables() {
        let a = Type::variable_id(0);
        let b = Type::variable_id(1);
        let constraints = [dependency(a, b), dependency(b, a)];
        let mut inference = UnifiedTypeInference::new_with_ty_vars(2);
        assert_eq!(
            reduction_rigid_types(&constraints, &[], &mut inference),
            vec![a, b]
        );
        assert_eq!(
            reduction_rigid_types(&constraints, &[a], &mut inference),
            vec![a]
        );
    }
}
