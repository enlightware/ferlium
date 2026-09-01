// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use ustr::Ustr;

use crate::{
    FxHashMap, FxHashSet,
    format::FormatWith,
    module::{
        EvidenceBindingId, ExtraParameterId, LocalFunctionId, ModuleEnv,
        PendingGeneratedStructuralProjectionSubscripts, SubscriptId, TraitDictionaryId, TraitId,
        id::Id,
    },
    types::{
        effects::{EffType, EffectVar},
        mutability::MutType,
        trait_solver::{TraitSolver, alpha_canonicalize_dictionary_requirements},
        r#type::{FnType, SubscriptType, Type, TypeVar},
        type_like::{TypeLike, instantiate_effect_types_in_place, instantiate_types_in_place},
        type_mapper::TypeMapper,
        type_scheme::ProjectionRequirementKind,
        type_scheme_display::format_have_trait,
    },
};

/// A dictionary requirement, that will be passed as extra parameter to a function.
#[derive(Clone, Debug)]
pub enum DictionaryReq {
    ProjectionSubscript {
        requirement: ProjectionRequirementKind,
        field: Ustr,
        subscript_ty: SubscriptType,
    },
    /// Runtime storage-mode evidence for a specific open variant case.
    ///
    /// The runtime parameter is one boolean determined by `variant_ty` and `tag`.
    /// `payload_ty` is retained as compile-time identity metadata for late recursive-call
    /// elaboration.
    VariantPayloadIndirection {
        variant_ty: Type,
        tag: Ustr,
        payload_ty: Type,
    },
    TraitImpl {
        trait_id: TraitId,
        input_tys: Vec<Type>,
        output_tys: Vec<Type>, // stored here for type generation, but not used in comparisons
        // FIXME: maybe we need a span here for proper error reporting
        output_effs: Vec<EffType>, // stored here for type generation, but not used in comparisons
    },
}

impl DictionaryReq {
    pub fn new_projection_subscript(
        requirement: ProjectionRequirementKind,
        field: Ustr,
        subscript_ty: SubscriptType,
    ) -> Self {
        Self::ProjectionSubscript {
            requirement,
            field,
            subscript_ty,
        }
    }

    /// Equality for dictionary-construction schemas, including trait outputs and output effects.
    ///
    /// [`PartialEq`] intentionally ignores those outputs for requirement lookup and must not be
    /// used to verify the ABI of a selected dictionary definition.
    pub(crate) fn same_capture_schema_entry(&self, other: &Self) -> bool {
        use DictionaryReq::*;
        match (self, other) {
            (
                ProjectionSubscript {
                    requirement,
                    field,
                    subscript_ty,
                },
                ProjectionSubscript {
                    requirement: other_requirement,
                    field: other_field,
                    subscript_ty: other_subscript_ty,
                },
            ) => {
                requirement == other_requirement
                    && field == other_field
                    && subscript_ty == other_subscript_ty
            }
            (
                VariantPayloadIndirection {
                    variant_ty,
                    tag,
                    payload_ty,
                },
                VariantPayloadIndirection {
                    variant_ty: other_variant_ty,
                    tag: other_tag,
                    payload_ty: other_payload_ty,
                },
            ) => {
                variant_ty == other_variant_ty && tag == other_tag && payload_ty == other_payload_ty
            }
            (
                TraitImpl {
                    trait_id,
                    input_tys,
                    output_tys,
                    output_effs,
                },
                TraitImpl {
                    trait_id: other_trait_id,
                    input_tys: other_input_tys,
                    output_tys: other_output_tys,
                    output_effs: other_output_effs,
                },
            ) => {
                trait_id == other_trait_id
                    && input_tys == other_input_tys
                    && output_tys == other_output_tys
                    && output_effs == other_output_effs
            }
            _ => false,
        }
    }

    pub fn new_trait_impl(
        trait_id: TraitId,
        input_tys: Vec<Type>,
        output_tys: Vec<Type>,
        output_effs: Vec<EffType>,
    ) -> Self {
        Self::TraitImpl {
            trait_id,
            input_tys,
            output_tys,
            output_effs,
        }
    }

    pub fn new_variant_payload_indirection(variant_ty: Type, tag: Ustr, payload_ty: Type) -> Self {
        Self::VariantPayloadIndirection {
            variant_ty,
            tag,
            payload_ty,
        }
    }

    /// Instantiate self with a caller-supplied mapper.
    pub(crate) fn instantiate<M: TypeMapper>(&self, mapper: &mut M) -> DictionaryReq {
        let mut req = self.clone();
        req.instantiate_in_place(mapper);
        req
    }

    /// Instantiate self in place with a caller-supplied mapper.
    pub(crate) fn instantiate_in_place<M: TypeMapper>(&mut self, mapper: &mut M) {
        use DictionaryReq::*;
        match self {
            ProjectionSubscript { subscript_ty, .. } => {
                *subscript_ty = subscript_ty.map(mapper);
            }
            VariantPayloadIndirection {
                variant_ty,
                payload_ty,
                ..
            } => {
                *variant_ty = variant_ty.map(mapper);
                *payload_ty = payload_ty.map(mapper);
            }
            TraitImpl {
                input_tys,
                output_tys,
                output_effs,
                ..
            } => {
                instantiate_types_in_place(input_tys, mapper);
                instantiate_types_in_place(output_tys, mapper);
                instantiate_effect_types_in_place(output_effs, mapper);
            }
        }
    }

    pub fn to_dict_type(&self, trait_solver: &TraitSolver<'_>) -> Type {
        match self {
            DictionaryReq::ProjectionSubscript { subscript_ty, .. } => {
                Type::subscript_type(subscript_ty.clone())
            }
            DictionaryReq::VariantPayloadIndirection { .. } => Type::primitive::<bool>(),
            DictionaryReq::TraitImpl {
                trait_id,
                input_tys,
                output_tys,
                output_effs,
            } => trait_solver
                .trait_def(*trait_id)
                .get_dictionary_type_for_tys(input_tys, output_tys, output_effs),
        }
    }

    /// Returns the type of the dictionary value satisfying this requirement,
    /// resolving traits through `env`.
    pub fn to_dict_type_in_env(&self, env: &ModuleEnv<'_>) -> Type {
        match self {
            DictionaryReq::ProjectionSubscript { subscript_ty, .. } => {
                Type::subscript_type(subscript_ty.clone())
            }
            DictionaryReq::VariantPayloadIndirection { .. } => Type::primitive::<bool>(),
            DictionaryReq::TraitImpl {
                trait_id,
                input_tys,
                output_tys,
                output_effs,
            } => env.trait_def(*trait_id).get_dictionary_type_for_tys(
                input_tys,
                output_tys,
                output_effs,
            ),
        }
    }
}

impl PartialEq for DictionaryReq {
    fn eq(&self, other: &Self) -> bool {
        use DictionaryReq::*;
        match (self, other) {
            (
                ProjectionSubscript {
                    requirement: requirement1,
                    field: field1,
                    subscript_ty: subscript_ty1,
                },
                ProjectionSubscript {
                    requirement: requirement2,
                    field: field2,
                    subscript_ty: subscript_ty2,
                },
            ) => requirement1 == requirement2 && field1 == field2 && subscript_ty1 == subscript_ty2,
            (
                TraitImpl {
                    trait_id: tr1,
                    input_tys: in1,
                    ..
                },
                TraitImpl {
                    trait_id: tr2,
                    input_tys: in2,
                    ..
                },
            ) => tr1 == tr2 && in1 == in2,
            (
                VariantPayloadIndirection {
                    variant_ty: variant_ty1,
                    tag: tag1,
                    payload_ty: payload_ty1,
                },
                VariantPayloadIndirection {
                    variant_ty: variant_ty2,
                    tag: tag2,
                    payload_ty: payload_ty2,
                },
            ) => variant_ty1 == variant_ty2 && tag1 == tag2 && payload_ty1 == payload_ty2,
            _ => false,
        }
    }
}

impl Eq for DictionaryReq {}

impl FormatWith<ModuleEnv<'_>> for DictionaryReq {
    fn fmt_with(
        &self,
        f: &mut std::fmt::Formatter,
        env: &crate::module::ModuleEnv<'_>,
    ) -> std::fmt::Result {
        use DictionaryReq::*;
        match self {
            ProjectionSubscript {
                field,
                subscript_ty,
                ..
            } => write!(
                f,
                "{} projection {}: {}",
                subscript_ty.receiver_ty().format_with(env),
                field,
                Type::subscript_type(subscript_ty.clone()).format_with(env)
            ),
            VariantPayloadIndirection {
                variant_ty, tag, ..
            } => write!(
                f,
                "{} variant {tag} payload indirection",
                variant_ty.format_with(env)
            ),
            TraitImpl {
                trait_id,
                input_tys,
                output_tys,
                output_effs,
            } => format_have_trait(*trait_id, input_tys, output_tys, output_effs, f, env),
        }
    }
}

pub type DictionariesReq = Vec<DictionaryReq>;

/// Compile-time evidence embedded directly in a function evidence graph.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StaticEvidence {
    Dictionary {
        definition: TraitDictionaryId,
        captures: Box<[StaticEvidence]>,
    },
    Subscript {
        definition: SubscriptId,
        captures: Box<[StaticEvidence]>,
    },
    VariantPayloadStorage(bool),
}

impl StaticEvidence {
    pub(crate) fn bare_dictionary(definition: TraitDictionaryId) -> Self {
        Self::Dictionary {
            definition,
            captures: Box::new([]),
        }
    }
}

/// Origin of an immutable hidden-evidence binding.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EvidenceBindingSource {
    Parameter(ExtraParameterId),
    Static(StaticEvidence),
    ConstructedDictionary {
        definition: TraitDictionaryId,
        captures: Vec<EvidenceBindingId>,
    },
    ConstructedSubscript {
        definition: SubscriptId,
        captures: Vec<EvidenceBindingId>,
    },
}

/// One node in a function-scoped, dependency-ordered evidence graph.
#[derive(Clone, Debug)]
pub struct EvidenceBinding {
    pub requirement: DictionaryReq,
    pub source: EvidenceBindingSource,
}

/// Data structure to hold extra parameters for a function.
#[derive(Clone, Debug)]
pub struct ExtraParameters {
    /// The dictionary requirements for the function.
    /// This is a list of dictionaries that will be passed as extra parameters to the function.
    pub requirements: Vec<DictionaryReq>,
    /// A map from type variables to other type variables containing their representation type.
    /// This is used to resolve type variables when looking up field dict indices.
    pub repr_map: FxHashMap<TypeVar, TypeVar>,
}

impl ExtraParameters {
    pub fn is_empty(&self) -> bool {
        self.requirements.is_empty()
    }
    pub fn len(&self) -> usize {
        self.requirements.len()
    }
}

pub fn find_projection_subscript_dict_index(
    dicts: &ExtraParameters,
    var: TypeVar,
    field: &str,
) -> Option<usize> {
    // Resolve the variable to its representation type if it is a different type variable.
    let var = dicts.repr_map.get(&var).unwrap_or(&var);
    let ty = Type::variable(*var);
    // Find the index of the dictionary that matches the type and field.
    dicts.requirements.iter().position(|dict| {
        if let DictionaryReq::ProjectionSubscript {
            field: field2,
            subscript_ty,
            ..
        } = &dict
        {
            subscript_ty.receiver_ty() == ty && field2 == field
        } else {
            false
        }
    })
}

pub fn find_projection_subscript_dict_index_for_receiver_ty(
    dicts: &ExtraParameters,
    receiver_ty: Type,
    field: &str,
) -> Option<usize> {
    dicts.requirements.iter().position(|dict| {
        if let DictionaryReq::ProjectionSubscript {
            field: requirement_field,
            subscript_ty,
            ..
        } = dict
        {
            subscript_ty.receiver_ty() == receiver_ty && requirement_field == field
        } else {
            false
        }
    })
}

pub fn find_variant_payload_indirection_index(
    dicts: &ExtraParameters,
    variant_ty: Type,
    tag: Ustr,
) -> Option<usize> {
    dicts.requirements.iter().position(|dict| {
        matches!(
            dict,
            DictionaryReq::VariantPayloadIndirection {
                variant_ty: requirement_variant_ty,
                tag: requirement_tag,
                ..
            } if *requirement_variant_ty == variant_ty
                && *requirement_tag == tag
        )
    })
}

pub fn find_trait_impl_dict_index(
    dicts: &ExtraParameters,
    trait_id: TraitId,
    input_tys: &[Type],
) -> Option<usize> {
    let exact = dicts.requirements.iter().position(|dict| {
        if let DictionaryReq::TraitImpl {
            trait_id: trait_id2,
            input_tys: tys2,
            ..
        } = dict
        {
            input_tys == tys2 && trait_id == *trait_id2
        } else {
            false
        }
    });
    // Function effects constrain where a function value may be called, but they do not
    // distinguish runtime trait dictionaries for otherwise identical function-typed inputs.
    exact.or_else(|| {
        dicts.requirements.iter().position(|dict| {
            if let DictionaryReq::TraitImpl {
                trait_id: trait_id2,
                input_tys: tys2,
                ..
            } = dict
            {
                trait_id == *trait_id2 && same_types_erasing_effects(input_tys, tys2)
            } else {
                false
            }
        })
    })
}

fn same_types_erasing_effects(left: &[Type], right: &[Type]) -> bool {
    if left.len() != right.len() {
        return false;
    }

    left.iter()
        .map(|ty| erase_type_effects(*ty))
        .eq(right.iter().map(|ty| erase_type_effects(*ty)))
}

fn erase_type_effects(ty: Type) -> Type {
    ty.map(&mut EraseEffectsMapper)
}

struct EraseEffectsMapper;

impl TypeMapper for EraseEffectsMapper {
    fn map_type(&mut self, ty: Type) -> Type {
        ty
    }

    fn map_mut_type(&mut self, mut_ty: MutType) -> MutType {
        mut_ty
    }

    fn map_effect_type(&mut self, _eff_ty: &EffType) -> EffType {
        EffType::empty()
    }
}

pub(crate) fn instantiate_dictionary_requirements<M: TypeMapper>(
    dicts: &DictionariesReq,
    mapper: &mut M,
) -> DictionariesReq {
    dicts.iter().map(|dict| dict.instantiate(mapper)).collect()
}

/// Final generic information needed to elaborate calls inferred before a recursive callee's
/// constraints were known.
#[derive(Clone, Debug)]
pub struct LateFunctionInstData {
    pub requirements: ExtraParameters,
    pub fn_ty: FnType,
    /// Final normalized effect quantifiers. Preliminary recursive calls do not always record them,
    /// so late elaboration can reconstruct their instantiation from the function surface.
    pub effect_quantifiers: Vec<EffectVar>,
}

/// Recursive functions in the current module can be called before their final requirements are
/// known. Elaboration replays those requirements against the final callee type and call-site type.
pub type ModuleInstData = FxHashMap<LocalFunctionId, LateFunctionInstData>;

/// Shared context for dictionary and value-dispatch elaboration.
pub struct DictElaborationCtx<'d, 'sr, 'sm> {
    /// The dictionaries for the current expression being elaborated.
    pub dicts: &'d ExtraParameters,
    /// The dictionaries for the current module, if compiling a module.
    /// None if compiling an expression.
    pub module_inst_data: Option<&'d ModuleInstData>,
    /// The trait solver. The borrow lifetime is independent from `dicts`.
    pub trait_solver: &'sr mut TraitSolver<'sm>,
    /// Generated structural projection subscripts needed while elaborating this function.
    pub(crate) generated_projection_subscripts:
        Option<PendingGeneratedStructuralProjectionSubscripts>,
    /// Function-scoped hidden evidence, in dependency order.
    pub evidence_bindings: Vec<EvidenceBinding>,
    /// Effect variables quantified by the callable currently being elaborated.
    pub(crate) retained_effect_vars: FxHashSet<EffectVar>,
}

impl<'d, 'sr, 'sm> DictElaborationCtx<'d, 'sr, 'sm> {
    pub(crate) fn new_with_generated_projection_subscripts(
        dicts: &'d ExtraParameters,
        module_inst_data: Option<&'d ModuleInstData>,
        trait_solver: &'sr mut TraitSolver<'sm>,
        generated_projection_subscripts: PendingGeneratedStructuralProjectionSubscripts,
    ) -> Self {
        let mut this = Self {
            dicts,
            module_inst_data,
            trait_solver,
            generated_projection_subscripts: Some(generated_projection_subscripts),
            evidence_bindings: Vec::new(),
            retained_effect_vars: FxHashSet::default(),
        };
        this.reset_evidence_bindings();
        this
    }

    /// Start an evidence graph with one parameter binding per inferred requirement.
    pub(crate) fn reset_evidence_bindings(&mut self) {
        self.evidence_bindings = self
            .dicts
            .requirements
            .iter()
            .cloned()
            .enumerate()
            .map(|(index, requirement)| EvidenceBinding {
                requirement,
                source: EvidenceBindingSource::Parameter(ExtraParameterId::from_index(index)),
            })
            .collect();
    }

    pub(crate) fn set_retained_effect_vars(&mut self, variables: FxHashSet<EffectVar>) {
        self.retained_effect_vars = variables;
    }

    pub(crate) fn static_evidence(&self, binding: EvidenceBindingId) -> Option<StaticEvidence> {
        match &self.evidence_bindings[binding.as_index()].source {
            EvidenceBindingSource::Static(evidence) => Some(evidence.clone()),
            EvidenceBindingSource::Parameter(_)
            | EvidenceBindingSource::ConstructedDictionary { .. }
            | EvidenceBindingSource::ConstructedSubscript { .. } => None,
        }
    }

    /// Verify the function-scoped evidence graph and selected dictionary ABIs.
    pub(crate) fn assert_evidence_bindings_valid(&self) {
        let mut saw_non_parameter = false;
        for (index, binding) in self.evidence_bindings.iter().enumerate() {
            if let EvidenceBindingSource::Parameter(parameter) = &binding.source {
                assert!(
                    !saw_non_parameter && parameter.as_index() == index,
                    "evidence parameters must form an identity-indexed graph prefix"
                );
            } else {
                saw_non_parameter = true;
            }
            let captures = match &binding.source {
                EvidenceBindingSource::ConstructedDictionary { captures, .. }
                | EvidenceBindingSource::ConstructedSubscript { captures, .. } => captures,
                EvidenceBindingSource::Parameter(_) | EvidenceBindingSource::Static(_) => {
                    continue;
                }
            };
            assert!(
                captures.iter().all(|capture| capture.as_index() < index),
                "evidence binding {index} must refer only to earlier bindings"
            );

            let EvidenceBindingSource::ConstructedDictionary {
                definition,
                captures,
            } = &binding.source
            else {
                continue;
            };
            let expected = self
                .trait_solver
                .get_impl_data_by_id(crate::module::TraitImplId::new(
                    definition.module_id,
                    definition.impl_id,
                ))
                .dictionary_value
                .capture_schema();
            assert_eq!(
                captures.len(),
                expected.len(),
                "constructed dictionary capture count does not match its definition"
            );
            let actual = captures
                .iter()
                .map(|capture| {
                    self.evidence_bindings[capture.as_index()]
                        .requirement
                        .clone()
                })
                .collect::<Vec<_>>();
            let actual = alpha_canonicalize_dictionary_requirements(&actual);
            let expected = alpha_canonicalize_dictionary_requirements(expected);
            assert!(
                actual
                    .iter()
                    .zip(&expected)
                    .all(|(actual, expected)| actual.same_capture_schema_entry(expected)),
                "constructed dictionary captures do not match its definition's canonical schema"
            );
        }
    }

    /// Reuse an identical selected artifact and ordered capture list within this function.
    ///
    /// Construction identity is entirely described by `source`. The requirement retained on the
    /// first binding is descriptive type information for later lowering/defaulting; every caller
    /// interning the same source must therefore describe the same evidence type.
    pub(crate) fn intern_evidence_binding(
        &mut self,
        requirement: DictionaryReq,
        source: EvidenceBindingSource,
    ) -> EvidenceBindingId {
        if let Some(index) = self
            .evidence_bindings
            .iter()
            .position(|binding| binding.source == source)
        {
            return EvidenceBindingId::from_index(index);
        }
        let id = EvidenceBindingId::from_index(self.evidence_bindings.len());
        self.evidence_bindings.push(EvidenceBinding {
            requirement,
            source,
        });
        id
    }

    pub(crate) fn take_generated_projection_subscripts(
        &mut self,
    ) -> Option<PendingGeneratedStructuralProjectionSubscripts> {
        self.generated_projection_subscripts.take()
    }
}
