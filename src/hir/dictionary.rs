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
    FxHashMap,
    format::FormatWith,
    module::{LocalFunctionId, ModuleEnv, PendingGeneratedStructuralProjectionSubscripts, TraitId},
    types::{
        effects::{EffType, EffectVar},
        mutability::MutType,
        trait_solver::TraitSolver,
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
    /// Runtime layout evidence for constructing an open generic variant case.
    VariantPayloadStorage {
        variant_ty: Type,
        tag: Ustr,
        /// Compile-time identity metadata for late recursive-call elaboration. The runtime
        /// evidence remains one boolean determined by `variant_ty` and `tag`.
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

    pub fn new_variant_payload_storage(variant_ty: Type, tag: Ustr, payload_ty: Type) -> Self {
        Self::VariantPayloadStorage {
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
            VariantPayloadStorage {
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
            DictionaryReq::VariantPayloadStorage { .. } => Type::primitive::<bool>(),
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
            DictionaryReq::VariantPayloadStorage { .. } => Type::primitive::<bool>(),
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
                VariantPayloadStorage {
                    variant_ty: variant_ty1,
                    tag: tag1,
                    ..
                },
                VariantPayloadStorage {
                    variant_ty: variant_ty2,
                    tag: tag2,
                    ..
                },
            ) => variant_ty1 == variant_ty2 && tag1 == tag2,
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
            VariantPayloadStorage {
                variant_ty, tag, ..
            } => write!(
                f,
                "{} variant {tag} payload storage",
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

pub fn find_variant_payload_storage_index(
    dicts: &ExtraParameters,
    variant_ty: Type,
    tag: Ustr,
) -> Option<usize> {
    dicts.requirements.iter().position(|dict| {
        matches!(
            dict,
            DictionaryReq::VariantPayloadStorage {
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
}

impl<'d, 'sr, 'sm> DictElaborationCtx<'d, 'sr, 'sm> {
    pub(crate) fn new_with_generated_projection_subscripts(
        dicts: &'d ExtraParameters,
        module_inst_data: Option<&'d ModuleInstData>,
        trait_solver: &'sr mut TraitSolver<'sm>,
        generated_projection_subscripts: PendingGeneratedStructuralProjectionSubscripts,
    ) -> Self {
        Self {
            dicts,
            module_inst_data,
            trait_solver,
            generated_projection_subscripts: Some(generated_projection_subscripts),
        }
    }

    pub(crate) fn take_generated_projection_subscripts(
        &mut self,
    ) -> Option<PendingGeneratedStructuralProjectionSubscripts> {
        self.generated_projection_subscripts.take()
    }
}
