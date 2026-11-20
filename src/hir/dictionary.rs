// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use std::fmt;

use ustr::Ustr;

use crate::{
    FxHashMap, FxHashSet, Location,
    format::FormatWith,
    module::{
        EvidenceBindingId, ExtraParameterId, LocalFunctionId, LocalSubscriptId, ModuleEnv,
        PendingGeneratedStructuralProjectionSubscripts, SubscriptId, TraitDictionaryId, TraitId,
        TraitImplId, id::Id,
    },
    std::value::{TypeLayoutEnv, VariantPayloadStorageDecision, variant_payload_storage_decision},
    types::{
        effects::{EffType, EffectVar},
        r#trait::{Trait, TraitParentSlotIndex},
        trait_solver::{EvidencePlan, TraitSolver, alpha_canonicalize_dictionary_requirements},
        r#type::{SubscriptType, Type, TypeVar},
        type_like::{TypeLike, instantiate_effect_types_in_place, instantiate_types_in_place},
        type_mapper::TypeMapper,
        type_matching::erase_type_effects,
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
    /// `payload_ty` is compile-time identity metadata.
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

    /// Whether a trait requirement is closed: no type or effect variable in its types or output
    /// effects. A closed requirement has one static dictionary, which selection gives; an open
    /// one depends on its variables, effects included, as the effects of the methods do.
    pub(crate) fn is_closed(&self) -> bool {
        match self {
            Self::TraitImpl {
                input_tys,
                output_tys,
                output_effs,
                ..
            } => {
                input_tys
                    .iter()
                    .chain(output_tys)
                    .all(TypeLike::is_constant)
                    && output_effs.iter().all(|effects| !effects.has_variables())
            }
            Self::ProjectionSubscript { .. } | Self::VariantPayloadIndirection { .. } => false,
        }
    }

    /// Exact contract identity, including fixed effect bounds. Used when attaching a recorded
    /// construction to a particular request, rather than looking up interchangeable evidence.
    pub(crate) fn same_contract(&self, other: &Self) -> bool {
        if !self.same_capture_schema_entry(other) {
            return false;
        }
        match (self, other) {
            (
                Self::TraitImpl { output_effs, .. },
                Self::TraitImpl {
                    output_effs: other, ..
                },
            ) => output_effs == other,
            _ => true,
        }
    }

    /// Equality for dictionary-construction schemas, including trait outputs and output effects
    /// with variables.
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
                // Fixed output effects are bounds the dictionary fits, not part of its identity.
                trait_id == other_trait_id
                    && input_tys == other_input_tys
                    && output_tys == other_output_tys
                    && output_effs
                        .iter()
                        .zip(other_output_effs)
                        .all(|(eff, other)| {
                            eff == other || (!eff.has_variables() && !other.has_variables())
                        })
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

    /// Whether this is a trait requirement without type or effect variables.
    pub(crate) fn is_ground_trait_impl(&self) -> bool {
        match self {
            Self::TraitImpl {
                input_tys,
                output_tys,
                output_effs,
                ..
            } => {
                input_tys.iter().chain(output_tys).all(Type::is_constant)
                    && !output_effs.iter().any(EffType::has_variables)
            }
            _ => false,
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
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &ModuleEnv<'_>) -> fmt::Result {
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
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StaticEvidence {
    /// A dictionary closed over static captures. `ty_args` are the arguments of its
    /// implementation's type parameters ([`TraitImpl::ty_params`]), with effects erased: captures
    /// need not determine all of them, and effects never distinguish dictionaries. Build it with
    /// [`StaticEvidence::dictionary`].
    ///
    /// [`TraitImpl::ty_params`]: crate::module::TraitImpl::ty_params
    Dictionary {
        definition: TraitDictionaryId,
        ty_args: Box<[Type]>,
        captures: Box<[StaticEvidence]>,
    },
    Subscript {
        definition: SubscriptId,
        captures: Box<[StaticEvidence]>,
    },
    VariantPayloadStorage(bool),
}

impl StaticEvidence {
    pub(crate) fn dictionary(
        definition: TraitDictionaryId,
        ty_args: &[Type],
        captures: Box<[StaticEvidence]>,
    ) -> Self {
        Self::Dictionary {
            definition,
            ty_args: ty_args.iter().copied().map(erase_type_effects).collect(),
            captures,
        }
    }
}

/// Origin of an immutable hidden-evidence binding.
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
    /// The dictionary in parent slot `index` of the trait dictionary `dictionary`.
    Parent {
        dictionary: EvidenceBindingId,
        index: TraitParentSlotIndex,
    },
}

/// One node in a function-scoped, dependency-ordered evidence graph.
#[derive(Clone, Debug)]
pub struct EvidenceBinding {
    pub requirement: DictionaryReq,
    pub source: EvidenceBindingSource,
}

/// Data structure to hold extra parameters for a function.
#[derive(Clone, Debug, Default)]
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

impl ExtraParameters {
    /// The parameter that gives the function the evidence of `requirement`, if it is given
    /// it. Evidence that a function is given is taken as it is, whatever the type: that of a
    /// type that is open here, and that of a known type, as an entry of a dictionary made for
    /// a known type is given what its implementation requires at that type.
    pub fn given(&self, requirement: &DictionaryReq) -> Option<usize> {
        match requirement {
            DictionaryReq::ProjectionSubscript {
                field,
                subscript_ty,
                ..
            } => self.given_field(subscript_ty.receiver_ty(), field),
            DictionaryReq::VariantPayloadIndirection { .. } => self
                .requirements
                .iter()
                .position(|given| given == requirement),
            DictionaryReq::TraitImpl {
                trait_id,
                input_tys,
                output_tys,
                ..
            } => self.given_trait_impl(*trait_id, input_tys, output_tys),
        }
    }

    /// As [`Self::given`], for the field `field` of `receiver_ty`. A type variable stands
    /// for its representation, if the function has one for it.
    pub fn given_field(&self, receiver_ty: Type, field: &str) -> Option<usize> {
        let open = receiver_ty.data().as_variable().copied();
        let receiver_ty = match open {
            Some(var) => Type::variable(*self.repr_map.get(&var).unwrap_or(&var)),
            None => receiver_ty,
        };
        self.requirements.iter().position(|requirement| {
            matches!(
                requirement,
                DictionaryReq::ProjectionSubscript {
                    field: given_field,
                    subscript_ty,
                    ..
                } if subscript_ty.receiver_ty() == receiver_ty && given_field == field
            )
        })
    }

    /// As [`Self::given`], for where a payload is stored: `requirement` is in the canonical form
    /// of [`variant_payload_storage_decision`]. A given requirement is the same decision when its
    /// canonical form is equal, as a scheme may name the variant otherwise, such as `Option<T>`
    /// for its shape.
    pub(crate) fn given_variant_payload_storage(
        &self,
        requirement: &DictionaryReq,
        env: &impl TypeLayoutEnv,
    ) -> Option<usize> {
        self.requirements.iter().position(|given| {
            let DictionaryReq::VariantPayloadIndirection {
                variant_ty,
                tag,
                payload_ty,
            } = given
            else {
                return false;
            };
            given == requirement
                || matches!(
                    variant_payload_storage_decision(
                        *variant_ty,
                        *tag,
                        *payload_ty,
                        Location::new_synthesized(),
                        env,
                    ),
                    Ok(VariantPayloadStorageDecision::Evidence(canonical)) if canonical == *requirement
                )
        })
    }

    /// As [`Self::given`], for the dictionary of `trait_id` for `input_tys`, whose outputs are
    /// `output_tys`: see [`same_application_erasing_effects`].
    pub fn given_trait_impl(
        &self,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: &[Type],
    ) -> Option<usize> {
        self.given_trait_impl_matching(trait_id, &|inputs, _| inputs == input_tys)
            .or_else(|| {
                self.given_trait_impl_matching(trait_id, &|inputs, outputs| {
                    same_application_erasing_effects(inputs, outputs, input_tys, output_tys)
                })
            })
    }

    /// The first dictionary of `trait_id` that the function is given whose input and output
    /// types `same` accepts.
    fn given_trait_impl_matching(
        &self,
        trait_id: TraitId,
        same: &dyn Fn(&[Type], &[Type]) -> bool,
    ) -> Option<usize> {
        self.requirements.iter().position(|requirement| {
            matches!(
                requirement,
                DictionaryReq::TraitImpl {
                    trait_id: given_trait_id,
                    input_tys: given_input_tys,
                    output_tys: given_output_tys,
                    ..
                } if *given_trait_id == trait_id && same(given_input_tys, given_output_tys)
            )
        })
    }
}

/// A requirement that a [`ParentWalk`] reaches, and how.
#[derive(Debug)]
pub(crate) struct ParentNode {
    pub requirement: DictionaryReq,
    pub reached: Reached,
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum Reached {
    /// A root, with the caller's index.
    Root(usize),
    /// Parent slot `index` of the dictionary of the earlier node `holder`.
    Slot {
        holder: usize,
        index: TraitParentSlotIndex,
    },
}

/// A walk over the roots that are trait dictionaries, then the requirements that their
/// dictionaries hold in their parent slots, transitively, breadth first. It yields the index of
/// each node as it reaches it, and adds the slots of a node only when the earlier nodes are
/// yielded. A requirement of the trait
/// and the input types of an earlier node, which determine its outputs, is not added again, so
/// the walk ends: a trait only implies traits defined before it. Requirements that differ only
/// by the effects of their types are kept apart: each holds its own slots.
///
/// Contract reduction (which implied requirements the slots hold) and evidence lookup (from which
/// slot to read one) both walk the slots with this, so that they reach the same requirements.
pub(crate) struct ParentWalk<'t, D: Fn(TraitId) -> &'t Trait> {
    nodes: Vec<ParentNode>,
    /// The next node to yield.
    next: usize,
    /// The next node whose slots to add.
    holder: usize,
    trait_def: D,
}

impl<'t, D: Fn(TraitId) -> &'t Trait> ParentWalk<'t, D> {
    pub(crate) fn new(
        roots: impl IntoIterator<Item = (usize, DictionaryReq)>,
        trait_def: D,
    ) -> Self {
        let mut walk = Self {
            nodes: Vec::new(),
            next: 0,
            holder: 0,
            trait_def,
        };
        for (root, requirement) in roots {
            if matches!(requirement, DictionaryReq::TraitImpl { .. }) {
                walk.push(requirement, Reached::Root(root));
            }
        }
        walk
    }

    /// All the nodes, once the walk has reached them.
    pub(crate) fn into_all_nodes(mut self) -> Vec<ParentNode> {
        while self.next().is_some() {}
        self.nodes
    }

    fn push(&mut self, requirement: DictionaryReq, reached: Reached) {
        if !self
            .nodes
            .iter()
            .any(|node| same_trait_application(&node.requirement, &requirement))
        {
            self.nodes.push(ParentNode {
                requirement,
                reached,
            });
        }
    }
}

impl<'t, D: Fn(TraitId) -> &'t Trait> Iterator for ParentWalk<'t, D> {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        while self.next == self.nodes.len() {
            let DictionaryReq::TraitImpl {
                trait_id,
                input_tys,
                output_tys,
                output_effs,
            } = &self.nodes.get(self.holder)?.requirement
            else {
                unreachable!("only trait dictionaries have parent slots")
            };
            let slots =
                (self.trait_def)(*trait_id).parent_slots(input_tys, output_tys, output_effs);
            let holder = self.holder;
            self.holder += 1;
            for (index, requirement) in slots.into_iter().enumerate() {
                let index = TraitParentSlotIndex::from_index(index);
                self.push(requirement, Reached::Slot { holder, index });
            }
        }
        self.next += 1;
        Some(self.next - 1)
    }
}

/// Whether two trait requirements are of the same trait at the same input types.
fn same_trait_application(left: &DictionaryReq, right: &DictionaryReq) -> bool {
    matches!((left, right), (
        DictionaryReq::TraitImpl { trait_id: left_trait, input_tys: left_inputs, .. },
        DictionaryReq::TraitImpl { trait_id: right_trait, input_tys: right_inputs, .. },
    ) if left_trait == right_trait && left_inputs == right_inputs)
}

/// Whether a given application, of `inputs` and `outputs`, is the requested one, of
/// `requested_inputs` and `requested_outputs`, up to the effects of their types. Function effects
/// constrain where a function value may be called, but they do not distinguish runtime trait
/// dictionaries for otherwise identical function-typed inputs, so the same application may be
/// seen with other effects; its output types then agree up to effects too. An application whose
/// outputs differ is another one, which another dictionary answers.
fn same_application_erasing_effects(
    inputs: &[Type],
    outputs: &[Type],
    requested_inputs: &[Type],
    requested_outputs: &[Type],
) -> bool {
    same_types_erasing_effects(inputs, requested_inputs)
        && same_types_erasing_effects(outputs, requested_outputs)
}

fn same_types_erasing_effects(left: &[Type], right: &[Type]) -> bool {
    if left.len() != right.len() {
        return false;
    }

    left.iter()
        .map(|ty| erase_type_effects(*ty))
        .eq(right.iter().map(|ty| erase_type_effects(*ty)))
}

pub(crate) fn instantiate_dictionary_requirements<M: TypeMapper>(
    dicts: &DictionariesReq,
    mapper: &mut M,
) -> DictionariesReq {
    dicts.iter().map(|dict| dict.instantiate(mapper)).collect()
}

/// What a reference inside a recursive group needs of the function that it names, and of the
/// function that makes it, once the group is final.
#[derive(Clone, Debug)]
pub struct LateFunctionInstData {
    pub requirements: ExtraParameters,
    /// The inference variable that each type quantifier was before the scheme was normalized, in
    /// the order of the quantifiers. The functions of a recursive group are inferred with one
    /// instance of each type, so two of them name one type by the same inference variable.
    pub ty_origins: Vec<TypeVar>,
    /// The inference variable that each effect quantifier was, in the same way.
    pub effect_origins: Vec<EffectVar>,
    /// Whether each reference to this function has effects of its own: it is a function of a
    /// group whose contracts were settled. Otherwise the function was inferred jointly with
    /// those that name it, or is a lambda of the function that names it, and they name an
    /// effect by the same inference variable, as they do a type.
    pub effects_per_reference: bool,
    /// For the references that the body of this function makes to functions that have effects
    /// per reference, by their site: the effects that the reference gives to the effect
    /// quantifiers of the function it names, in their order.
    pub reference_effects: FxHashMap<Location, Vec<EffType>>,
}

/// Recursive functions in the current module can be called before their final requirements are
/// known. Elaboration replays those requirements against the final callee type and call-site type.
#[derive(Default)]
pub struct ModuleInstData {
    pub functions: FxHashMap<LocalFunctionId, LateFunctionInstData>,
    /// For each subscript whose members are among these functions, one of them. The members of
    /// a subscript have one signature, so what one needs is what a value of the subscript needs.
    pub subscripts: FxHashMap<LocalSubscriptId, LocalFunctionId>,
}

/// Shared context for dictionary and value-dispatch elaboration.
pub struct DictElaborationCtx<'d, 'sr, 'sm> {
    pub(crate) evidence_plan: EvidencePlan,
    pub(crate) planned_bindings: Vec<Option<EvidenceBindingId>>,
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
    pub(crate) active_dictionary_constructions: Vec<DictionaryReq>,
    /// Effect variables quantified by the callable currently being elaborated.
    pub(crate) retained_effect_vars: FxHashSet<EffectVar>,
    /// The data of the function being elaborated; none outside a module, where no call is
    /// instantiated late.
    pub(crate) caller_inst_data: Option<&'d LateFunctionInstData>,
}

impl<'d, 'sr, 'sm> DictElaborationCtx<'d, 'sr, 'sm> {
    pub(crate) fn new_with_generated_projection_subscripts(
        dicts: &'d ExtraParameters,
        module_inst_data: Option<&'d ModuleInstData>,
        trait_solver: &'sr mut TraitSolver<'sm>,
        generated_projection_subscripts: PendingGeneratedStructuralProjectionSubscripts,
    ) -> Self {
        let mut this = Self {
            evidence_plan: Default::default(),
            planned_bindings: Vec::new(),
            dicts,
            module_inst_data,
            trait_solver,
            generated_projection_subscripts: Some(generated_projection_subscripts),
            evidence_bindings: Vec::new(),
            active_dictionary_constructions: Vec::new(),
            retained_effect_vars: FxHashSet::default(),
            caller_inst_data: None,
        };
        this.reset_evidence_bindings();
        this
    }

    pub(crate) fn set_evidence_plan(&mut self, mut plan: EvidencePlan) {
        plan.default_unquantified_effects(&self.retained_effect_vars);
        self.planned_bindings = vec![None; plan.nodes.len()];
        self.evidence_plan = plan;
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
            | EvidenceBindingSource::ConstructedSubscript { .. }
            | EvidenceBindingSource::Parent { .. } => None,
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
                EvidenceBindingSource::Parent { dictionary, .. } => {
                    assert!(
                        dictionary.as_index() < index,
                        "evidence binding {index} must refer only to earlier bindings"
                    );
                    continue;
                }
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
                .get_impl_data_by_id(TraitImplId::new(definition.module_id, definition.impl_id))
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

    /// Reuse an identical selected artifact, instantiation and capture list within this function.
    ///
    /// Captures need not determine all parameters of a generic dictionary. Preserve its use-site
    /// type even when two instantiations use the same artifact and capture list.
    pub(crate) fn intern_evidence_binding(
        &mut self,
        requirement: DictionaryReq,
        source: EvidenceBindingSource,
    ) -> EvidenceBindingId {
        if let Some(index) = self.evidence_bindings.iter().position(|binding| {
            binding.source == source && binding.requirement.same_capture_schema_entry(&requirement)
        }) {
            return EvidenceBindingId::from_index(index);
        }
        let id = EvidenceBindingId::from_index(self.evidence_bindings.len());
        self.evidence_bindings.push(EvidenceBinding {
            requirement,
            source,
        });
        id
    }

    /// The evidence of the trait `trait_id` at `input_tys`, whose outputs are `output_tys`, that
    /// the function is given: a dictionary that it takes, or one that their parent slots hold.
    /// This very application is searched for first, in both; one equal to it up to the effects
    /// of its types only then (see [`same_application_erasing_effects`]): such a match never
    /// hides an exact one.
    pub(crate) fn given_evidence(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: &[Type],
    ) -> Option<EvidenceBindingId> {
        let exact = |inputs: &[Type], _: &[Type]| inputs == input_tys;
        let erased = |inputs: &[Type], outputs: &[Type]| {
            same_application_erasing_effects(inputs, outputs, input_tys, output_tys)
        };
        // The slots are walked once, and only if a parameter does not answer exactly.
        let mut slots = None;
        for same in [&exact as &dyn Fn(&[Type], &[Type]) -> bool, &erased] {
            if let Some(index) = self.dicts.given_trait_impl_matching(trait_id, same) {
                return Some(EvidenceBindingId::from_index(index));
            }
            let nodes = slots.get_or_insert_with(|| self.parent_nodes());
            // The walk is breadth first: the first slot that holds it is on a shortest path.
            let found = nodes.iter().position(|node| {
                matches!((node.reached, &node.requirement), (
                    Reached::Slot { .. },
                    DictionaryReq::TraitImpl {
                        trait_id: slot_trait,
                        input_tys: slot_inputs,
                        output_tys: slot_outputs,
                        ..
                    },
                ) if *slot_trait == trait_id && same(slot_inputs, slot_outputs))
            });
            if let Some(found) = found {
                let nodes = slots.take().expect("the slots were walked");
                return Some(self.bind_parent_path(&nodes, found));
            }
        }
        None
    }

    /// The requirements that the parent slots of the dictionaries that the function is given
    /// hold, directly or through other parent slots, breadth first.
    ///
    /// The slots are walked as contract reduction (`held_by_dictionaries`) walks them, so this
    /// finds every requirement that reduction leaves to them.
    fn parent_nodes(&self) -> Vec<ParentNode> {
        ParentWalk::new(
            self.dicts
                .requirements
                .iter()
                .enumerate()
                .filter(|(_, requirement)| matches!(requirement, DictionaryReq::TraitImpl { .. }))
                .map(|(index, requirement)| (index, requirement.clone())),
            |id| self.trait_solver.trait_def(id),
        )
        .into_all_nodes()
    }

    /// Bind the path of parent slots from its parameter down to `nodes[found]`.
    fn bind_parent_path(&mut self, nodes: &[ParentNode], found: usize) -> EvidenceBindingId {
        let mut path = Vec::new();
        let mut node = found;
        let parameter = loop {
            match nodes[node].reached {
                Reached::Root(parameter) => break parameter,
                Reached::Slot { holder, index } => {
                    path.push((node, index));
                    node = holder;
                }
            }
        };
        let mut binding = EvidenceBindingId::from_index(parameter);
        for (node, index) in path.into_iter().rev() {
            binding = self.intern_evidence_binding(
                nodes[node].requirement.clone(),
                EvidenceBindingSource::Parent {
                    dictionary: binding,
                    index,
                },
            );
        }
        binding
    }

    pub(crate) fn take_generated_projection_subscripts(
        &mut self,
    ) -> Option<PendingGeneratedStructuralProjectionSubscripts> {
        self.generated_projection_subscripts.take()
    }
}
