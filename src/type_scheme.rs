// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{
    borrow::Borrow,
    collections::{BTreeMap, HashMap, HashSet},
    hash::{Hash, Hasher},
};

use crate::{
    Location,
    dictionary_passing::ExtraParameters,
    error::InternalCompilationError,
    format::{FormatWith, write_with_separator_and_format_fn},
    location::InstantiableLocation,
    std::core::REPR_TRAIT,
    r#trait::TraitRef,
    trait_solver::TraitSolver,
    type_inference::UnifiedTypeInference,
    type_like::TypeLike,
    type_mapper::TypeMapper,
    type_visitor::TypeInnerVisitor,
};
use enum_as_inner::EnumAsInner;
use itertools::Itertools;
use ustr::Ustr;

use crate::{
    dictionary_passing::{DictionaryReq, instantiate_dictionaries_req},
    effects::{EffType, EffectVar, EffectsSubstitution},
    format::FormatWithData,
    ir::FnInstData,
    module::ModuleEnv,
    r#type::{Type, TypeSubstitution, TypeVar},
    type_inference::{InstSubstitution, TypeInference},
};

/// The display style for type schemes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DisplayStyle {
    /// Explicitly show quantifiers and constraints in () and connected with ∧.
    Mathematical,
    /// Implicitly show quantifiers and constraints connected with , in a where clause.
    Rust,
}

/// A constraint that can be part of a type scheme.
/// This corresponds to a solved constraint in HM(X).
#[derive(Debug, Clone, Eq, EnumAsInner)]
pub enum PubTypeConstraint {
    /// Tuple projection constraint: tuple_ty.index = element_ty
    TupleAtIndexIs {
        tuple_ty: Type,
        tuple_span: InstantiableLocation,
        index: usize,
        index_span: InstantiableLocation,
        element_ty: Type,
    },
    /// Record field access constraint: record_ty.field = element_ty
    RecordFieldIs {
        record_ty: Type,
        record_span: InstantiableLocation,
        field: Ustr,
        field_span: InstantiableLocation,
        element_ty: Type,
    },
    /// Variant for type: variant_ty ⊇ tag(payload_ty)
    TypeHasVariant {
        variant_ty: Type,
        variant_span: InstantiableLocation,
        tag: Ustr,
        payload_ty: Type,
        payload_span: InstantiableLocation,
    },
    /// Types have trait
    HaveTrait {
        trait_ref: TraitRef,
        input_tys: Vec<Type>,
        output_tys: Vec<Type>,
        span: InstantiableLocation,
    },
}

impl PubTypeConstraint {
    pub fn new_tuple_at_index_is(
        tuple_ty: Type,
        tuple_span: Location,
        index: usize,
        index_span: Location,
        element_ty: Type,
    ) -> Self {
        Self::TupleAtIndexIs {
            tuple_ty,
            tuple_span: InstantiableLocation::new(tuple_span),
            index,
            index_span: InstantiableLocation::new(index_span),
            element_ty,
        }
    }

    pub fn new_record_field_is(
        record_ty: Type,
        record_span: Location,
        field: Ustr,
        field_span: Location,
        element_ty: Type,
    ) -> Self {
        Self::RecordFieldIs {
            record_ty,
            record_span: InstantiableLocation::new(record_span),
            field,
            field_span: InstantiableLocation::new(field_span),
            element_ty,
        }
    }

    pub fn new_type_has_variant(
        variant_ty: Type,
        variant_span: Location,
        tag: Ustr,
        payload_ty: Type,
        payload_span: Location,
    ) -> Self {
        Self::TypeHasVariant {
            variant_ty,
            variant_span: InstantiableLocation::new(variant_span),
            tag,
            payload_ty,
            payload_span: InstantiableLocation::new(payload_span),
        }
    }

    pub fn new_have_trait(
        trait_ref: TraitRef,
        input_tys: Vec<Type>,
        output_tys: Vec<Type>,
        span: Location,
    ) -> Self {
        assert_eq!(input_tys.len(), trait_ref.input_type_count() as usize);
        assert_eq!(output_tys.len(), trait_ref.output_type_count() as usize);
        Self::HaveTrait {
            trait_ref,
            input_tys,
            output_tys,
            span: InstantiableLocation::new(span),
        }
    }

    pub fn use_site(&self) -> Location {
        use PubTypeConstraint::*;
        match self {
            TupleAtIndexIs { tuple_span, .. } => tuple_span.use_site,
            RecordFieldIs { record_span, .. } => record_span.use_site,
            TypeHasVariant { variant_span, .. } => variant_span.use_site,
            HaveTrait { span, .. } => span.use_site,
        }
    }

    pub fn instantiate_location(&mut self, use_site: Location) {
        use PubTypeConstraint::*;
        match self {
            TupleAtIndexIs {
                tuple_span,
                index_span,
                ..
            } => {
                tuple_span.instantiate(use_site);
                index_span.instantiate(use_site);
            }
            RecordFieldIs {
                record_span,
                field_span,
                ..
            } => {
                record_span.instantiate(use_site);
                field_span.instantiate(use_site);
            }
            TypeHasVariant {
                payload_span: span, ..
            } => {
                span.instantiate(use_site);
            }
            HaveTrait { span, .. } => {
                span.instantiate(use_site);
            }
        }
    }

    pub fn instantiate_location_cloned(&self, use_site: Location) -> Self {
        let mut constraint = self.clone();
        constraint.instantiate_location(use_site);
        constraint
    }

    pub fn instantiate_and_drop_if_solved(
        &self,
        subst: &mut InstSubstitution,
        trait_solver: &mut TraitSolver<'_>,
    ) -> Result<Option<Self>, InternalCompilationError> {
        let constraint = self.instantiate(subst);
        use PubTypeConstraint::*;
        Ok(match &constraint {
            TupleAtIndexIs {
                tuple_ty,
                index,
                element_ty,
                ..
            } => {
                if tuple_ty.is_constant() && element_ty.is_constant() {
                    let tuple_ty_data = tuple_ty.data();
                    let tuple_data = tuple_ty_data.as_tuple().unwrap();
                    assert!(tuple_data.get(*index).unwrap() == element_ty);
                    None
                } else {
                    Some(constraint)
                }
            }
            RecordFieldIs {
                record_ty,
                field,
                element_ty,
                ..
            } => {
                if record_ty.is_constant() && element_ty.is_constant() {
                    let record_ty_data = record_ty.data();
                    let record_data = record_ty_data.as_record().unwrap();
                    assert!(record_data.iter().find(|t| t.0 == *field).unwrap().1 == *element_ty);
                    None
                } else {
                    Some(constraint)
                }
            }
            TypeHasVariant {
                variant_ty,
                tag,
                payload_ty,
                ..
            } => {
                if variant_ty.is_constant() && payload_ty.is_constant() {
                    let variant_ty_data = variant_ty.data();
                    let variant_data = variant_ty_data.as_variant().unwrap();
                    assert!(variant_data.iter().find(|t| t.0 == *tag).unwrap().1 == *payload_ty);
                    None
                } else {
                    Some(constraint)
                }
            }
            HaveTrait {
                trait_ref,
                input_tys,
                output_tys,
                span,
            } => {
                if input_tys.iter().all(Type::is_constant) {
                    let got_output_tys =
                        trait_solver.solve_output_types(trait_ref, input_tys, span.use_site)?;
                    assert_eq!(got_output_tys.len(), output_tys.len());
                    for (got_output_ty, output_ty) in got_output_tys.iter().zip(output_tys.iter()) {
                        let inner_ty_vars = output_ty.inner_ty_vars();
                        if inner_ty_vars.is_empty() {
                            assert_eq!(got_output_ty, output_ty);
                        } else {
                            // Unify the two types and get back the substitution
                            let ty_var_count = inner_ty_vars.len() as u32;
                            let ty_subst = (0..ty_var_count)
                                .map(|ty_var| {
                                    (inner_ty_vars[ty_var as usize], Type::variable_id(ty_var))
                                })
                                .collect::<TypeSubstitution>();
                            let local_subst = (ty_subst, EffectsSubstitution::new());
                            let mut ty_inf = UnifiedTypeInference::new_with_ty_vars(ty_var_count);
                            let output_ty = output_ty.instantiate(&local_subst);
                            ty_inf
                                .unify_same_type(
                                    *got_output_ty,
                                    span.use_site,
                                    output_ty,
                                    span.use_site,
                                )
                                .unwrap();
                            for (index, inner_ty_var) in inner_ty_vars.iter().enumerate() {
                                let ty = ty_inf.lookup_type_var(TypeVar::new(index as u32));
                                assert!(ty.is_constant());
                                subst.0.insert(*inner_ty_var, ty);
                            }
                        }
                    }
                    None
                } else {
                    Some(constraint)
                }
            }
        })
    }
}

impl TypeLike for PubTypeConstraint {
    fn map(&self, f: &mut impl TypeMapper) -> Self {
        use PubTypeConstraint::*;
        match self {
            TupleAtIndexIs {
                tuple_ty,
                tuple_span,
                index,
                index_span,
                element_ty,
            } => TupleAtIndexIs {
                tuple_ty: tuple_ty.map(f),
                tuple_span: tuple_span.clone(),
                index: *index,
                index_span: index_span.clone(),
                element_ty: element_ty.map(f),
            },
            RecordFieldIs {
                record_ty,
                record_span,
                field,
                field_span,
                element_ty,
            } => RecordFieldIs {
                record_ty: record_ty.map(f),
                record_span: record_span.clone(),
                field: *field,
                field_span: field_span.clone(),
                element_ty: element_ty.map(f),
            },
            TypeHasVariant {
                variant_ty,
                variant_span,
                tag,
                payload_ty,
                payload_span,
            } => TypeHasVariant {
                variant_ty: variant_ty.map(f),
                variant_span: variant_span.clone(),
                tag: *tag,
                payload_ty: payload_ty.map(f),
                payload_span: payload_span.clone(),
            },
            HaveTrait {
                trait_ref,
                input_tys,
                output_tys,
                span,
            } => HaveTrait {
                trait_ref: trait_ref.clone(),
                input_tys: input_tys.iter().map(|ty| ty.map(f)).collect(),
                output_tys: output_tys.iter().map(|ty| ty.map(f)).collect(),
                span: span.clone(),
            },
        }
    }

    fn visit(&self, visitor: &mut impl TypeInnerVisitor) {
        use PubTypeConstraint::*;
        match self {
            TupleAtIndexIs {
                tuple_ty,
                element_ty,
                ..
            } => {
                tuple_ty.data().visit(visitor);
                element_ty.data().visit(visitor);
            }
            RecordFieldIs {
                record_ty,
                element_ty,
                ..
            } => {
                record_ty.data().visit(visitor);
                element_ty.data().visit(visitor);
            }
            TypeHasVariant {
                variant_ty,
                payload_ty,
                ..
            } => {
                variant_ty.data().visit(visitor);
                payload_ty.data().visit(visitor);
            }
            HaveTrait {
                input_tys,
                output_tys,
                ..
            } => {
                for ty in input_tys {
                    ty.data().visit(visitor);
                }
                for ty in output_tys {
                    ty.data().visit(visitor);
                }
            }
        }
    }
}

impl TypeLike for Vec<PubTypeConstraint> {
    fn map(&self, f: &mut impl TypeMapper) -> Self {
        self.iter().map(|c| c.map(f)).collect()
    }

    fn visit(&self, visitor: &mut impl TypeInnerVisitor) {
        for c in self {
            c.visit(visitor);
        }
    }
}

impl PartialEq for PubTypeConstraint {
    fn eq(&self, other: &Self) -> bool {
        use PubTypeConstraint::*;
        match (self, other) {
            (
                TupleAtIndexIs {
                    tuple_ty: t_ty1,
                    index: idx1,
                    element_ty: e_ty1,
                    ..
                },
                TupleAtIndexIs {
                    tuple_ty: t_ty2,
                    index: idx2,
                    element_ty: e_ty2,
                    ..
                },
            ) => t_ty1 == t_ty2 && idx1 == idx2 && e_ty1 == e_ty2,
            (
                RecordFieldIs {
                    record_ty: r_ty1,
                    field: f1,
                    element_ty: e_ty1,
                    ..
                },
                RecordFieldIs {
                    record_ty: r_ty2,
                    field: f2,
                    element_ty: e_ty2,
                    ..
                },
            ) => r_ty1 == r_ty2 && f1 == f2 && e_ty1 == e_ty2,
            (
                TypeHasVariant {
                    variant_ty: v_ty1,
                    tag: tag1,
                    payload_ty: p_ty1,
                    ..
                },
                TypeHasVariant {
                    variant_ty: v_ty2,
                    tag: tag2,
                    payload_ty: p_ty2,
                    ..
                },
            ) => v_ty1 == v_ty2 && tag1 == tag2 && p_ty1 == p_ty2,
            (
                HaveTrait {
                    trait_ref: t1,
                    input_tys: i1,
                    output_tys: o1,
                    ..
                },
                HaveTrait {
                    trait_ref: t2,
                    input_tys: i2,
                    output_tys: o2,
                    ..
                },
            ) => t1 == t2 && i1 == i2 && o1 == o2,
            _ => false,
        }
    }
}

impl Hash for PubTypeConstraint {
    fn hash<H: Hasher>(&self, state: &mut H) {
        use PubTypeConstraint::*;
        match self {
            TupleAtIndexIs {
                tuple_ty,
                index,
                element_ty,
                ..
            } => {
                tuple_ty.hash(state);
                index.hash(state);
                element_ty.hash(state);
            }
            RecordFieldIs {
                record_ty,
                field,
                element_ty,
                ..
            } => {
                record_ty.hash(state);
                field.hash(state);
                element_ty.hash(state);
            }
            TypeHasVariant {
                variant_ty,
                tag,
                payload_ty,
                ..
            } => {
                variant_ty.hash(state);
                tag.hash(state);
                payload_ty.hash(state);
            }
            HaveTrait {
                trait_ref: r#trait,
                input_tys,
                output_tys,
                ..
            } => {
                r#trait.hash(state);
                for ty in input_tys {
                    ty.hash(state);
                }
                for ty in output_tys {
                    ty.hash(state);
                }
            }
        }
    }
}

impl FormatWith<ModuleEnv<'_>> for PubTypeConstraint {
    fn fmt_with(&self, f: &mut std::fmt::Formatter, env: &ModuleEnv<'_>) -> std::fmt::Result {
        use PubTypeConstraint::*;
        match self {
            TupleAtIndexIs {
                tuple_ty,
                index,
                element_ty,
                ..
            } => {
                write!(
                    f,
                    "{}.{} = {}",
                    tuple_ty.format_with(env),
                    index,
                    element_ty.format_with(env)
                )
            }
            RecordFieldIs {
                record_ty,
                field,
                element_ty,
                ..
            } => {
                write!(
                    f,
                    "{}.{} = {}",
                    record_ty.format_with(env),
                    field,
                    element_ty.format_with(env)
                )
            }
            TypeHasVariant {
                variant_ty,
                tag,
                payload_ty,
                ..
            } => {
                if *payload_ty == Type::unit() {
                    write!(f, "{} ⊇ {}", variant_ty.format_with(env), tag,)
                } else {
                    write!(
                        f,
                        "{} ⊇ {} {}",
                        variant_ty.format_with(env),
                        tag,
                        payload_ty.format_with(env)
                    )
                }
            }
            HaveTrait {
                trait_ref,
                input_tys,
                output_tys,
                ..
            } => format_have_trait(trait_ref, input_tys, output_tys, f, env),
        }
    }
}

/// Aggregated TypeHasVariant or RecordFieldIs constraints to be use for checking and display.
pub type VariantConstraint = BTreeMap<Ustr, Type>;
/// Aggregated TupleAtIndexIs constraints to be use for checking and display.
pub type TupleConstraint = BTreeMap<usize, Type>;

/// Aggregated constraint for display.
#[derive(EnumAsInner)]
enum AggregatedConstraint {
    Tuple(TupleConstraint),
    Record(VariantConstraint),
    Variant(VariantConstraint),
}

/// A type, with quantified type variables and associated constraints.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeScheme<Ty: TypeLike> {
    // for a compiled module, quantifiers should be equal to the type variables in the type
    // and the constraints.
    pub ty_quantifiers: Vec<TypeVar>,
    pub eff_quantifiers: HashSet<EffectVar>,
    pub ty: Ty,
    pub constraints: Vec<PubTypeConstraint>,
}

impl<Ty: TypeLike> TypeScheme<Ty> {
    /// Creates a new type scheme with no quantifier nor constraints.
    pub fn new_just_type(ty: Ty) -> Self {
        Self {
            ty_quantifiers: vec![],
            eff_quantifiers: HashSet::new(),
            ty,
            constraints: vec![],
        }
    }

    /// Creates a new type scheme by inferring quantifiers from the type, and no constraints.
    pub fn new_infer_quantifiers(ty: Ty) -> Self {
        let ty_quantifiers = ty.inner_ty_vars();
        let eff_quantifiers = ty.input_effect_vars();
        Self {
            ty_quantifiers,
            eff_quantifiers,
            ty,
            constraints: vec![],
        }
    }

    /// Creates a new type scheme by inferring quantifiers from the type, and some constraints.
    pub fn new_infer_quantifiers_with_constraints(
        ty: Ty,
        constraints: Vec<PubTypeConstraint>,
    ) -> Self {
        let ty_quantifiers = Self::list_ty_vars(&ty, constraints.iter());
        let eff_quantifiers = Self::list_eff_vars(&ty, constraints.iter());
        Self {
            ty_quantifiers,
            eff_quantifiers,
            ty,
            constraints,
        }
    }

    /// Returns the type quantifiers of this type scheme.
    pub(crate) fn ty_quantifiers_from_signature(&self) -> Vec<TypeVar> {
        Self::list_ty_vars(&self.ty, self.constraints.iter())
    }

    /// Returns whether there are no quantifiers nor constraints nor effects.
    pub fn is_just_type(&self) -> bool {
        self.is_just_type_and_effects() && self.eff_quantifiers.is_empty()
    }

    /// Returns whether there are no quantifiers nor constraints.
    pub fn is_just_type_and_effects(&self) -> bool {
        self.ty_quantifiers.is_empty() && self.constraints.is_empty()
    }

    /// Returns the type of this type scheme.
    pub fn ty(&self) -> &Ty {
        &self.ty
    }

    /// Returns the constraints of this type scheme.
    pub fn constraints(&self) -> &[PubTypeConstraint] {
        &self.constraints
    }

    /// Instantiates this type scheme with fresh type variables in ty_inf.
    /// If ty_var_count is not None, it will ensure having fresh type variables from 0 to ty_var_count-1.
    pub(crate) fn instantiate_with_fresh_vars(
        &self,
        ty_inf: &mut TypeInference,
        use_site: Location,
        ty_var_count: Option<u32>,
    ) -> (Ty, FnInstData, InstSubstitution) {
        let mut ty_subst = ty_inf.fresh_type_var_subst(&self.ty_quantifiers);
        let eff_subst = ty_inf.fresh_effect_var_subst(&self.eff_quantifiers);
        if let Some(ty_var_count) = ty_var_count {
            let mut ext_subst = HashMap::new();
            for ty_var_index in 0..ty_var_count {
                let ty_var = TypeVar::new(ty_var_index);
                if !ty_subst.contains_key(&ty_var) {
                    ext_subst.insert(ty_var, Type::variable(ty_inf.fresh_type_var()));
                }
            }
            ty_subst.extend(ext_subst);
        }
        let subst = (ty_subst, eff_subst);
        for constraint in &self.constraints {
            let mut constraint = constraint.instantiate(&subst);
            constraint.instantiate_location(use_site);
            ty_inf.add_pub_constraint(constraint);
        }
        let ty = self.ty.instantiate(&subst);
        let dict_req = instantiate_dictionaries_req(&self.extra_parameters().requirements, &subst);
        (ty, FnInstData::new(dict_req), subst)
    }

    /// Helper function to list free type variables in a type and its constraints.
    pub(crate) fn list_ty_vars(
        ty: &Ty,
        constraints: impl Iterator<Item = impl Borrow<PubTypeConstraint>>,
    ) -> Vec<TypeVar> {
        ty.inner_ty_vars()
            .into_iter()
            .chain(constraints.flat_map(|constraint| constraint.borrow().inner_ty_vars()))
            .unique()
            .collect()
    }

    /// Helper function to list free effect variables in a type and its constraints.
    pub(crate) fn list_eff_vars(
        ty: &Ty,
        constraints: impl Iterator<Item = impl Borrow<PubTypeConstraint>>,
    ) -> HashSet<EffectVar> {
        ty.inner_effect_vars()
            .into_iter()
            .chain(constraints.flat_map(|constraint| constraint.borrow().inner_effect_vars()))
            .unique()
            .collect()
    }

    pub(crate) fn normalize(&mut self) -> InstSubstitution {
        // Build a substitution that maps each type quantifier to a fresh type variable from 0.
        let ty_subst = normalize_types(&mut self.ty_quantifiers);

        // Build a substitution that maps each input effect quantifier to a fresh effect variable from 0.,
        // Note: in case of recursive functions, we might have output-only effects.
        // In this case, replace them with empty effects.
        let mut eff_subst = EffectsSubstitution::new();
        let input_effect_vars = self.ty.input_effect_vars();
        self.ty.output_effect_vars().iter().for_each(|var| {
            if !input_effect_vars.contains(var) {
                eff_subst.insert(*var, EffType::empty());
            }
        });
        self.eff_quantifiers = self
            .eff_quantifiers
            .iter()
            .enumerate()
            .map(|(i, var)| {
                let new_var = EffectVar::new(i as u32);
                eff_subst.insert(*var, EffType::single_variable(new_var));
                new_var
            })
            .collect();

        // Apply to type and constraints
        let subst = (ty_subst, eff_subst);
        self.ty = self.ty.instantiate(&subst);
        self.constraints = self
            .constraints
            .iter()
            .map(|constraint| constraint.instantiate(&subst))
            .collect();

        // Return
        subst
    }

    /// Remove constant constraints and simplify the type scheme.
    pub(crate) fn simplify(&mut self) {
        self.constraints.retain(|c| !c.is_constant());
        self.ty_quantifiers = Self::list_ty_vars(&self.ty, self.constraints.iter());
        self.eff_quantifiers = Self::list_eff_vars(&self.ty, self.constraints.iter());
    }

    /// Extra functions parameters that must be passed to resolve polymorphism.
    pub(crate) fn extra_parameters(&self) -> ExtraParameters {
        extra_parameters_from_constraints(&self.constraints)
    }

    pub(crate) fn format_quantifiers_math_style(
        &self,
        f: &mut std::fmt::Formatter,
    ) -> std::fmt::Result {
        let mut i = 0;
        for quantifier in &self.ty_quantifiers {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "∀")?;
            quantifier.format_math_style(f)?;
            i += 1;
        }
        for quantifier in self.eff_quantifiers.iter().sorted() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "∀{quantifier}")?;
            i += 1;
        }
        Ok(())
    }

    pub(crate) fn format_constraints(
        &self,
        style: DisplayStyle,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv<'_>,
    ) -> std::fmt::Result {
        format_constraints(&self.constraints, style, f, env)
    }

    pub(crate) fn format_quantifiers_and_constraints_math_style(
        &self,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv<'_>,
    ) -> std::fmt::Result {
        self.format_quantifiers_math_style(f)?;
        if !self.ty_quantifiers.is_empty() || !self.eff_quantifiers.is_empty() {
            write!(f, ".")?;
        }
        if !self.constraints.is_empty() {
            write!(f, " ")?;
        }
        self.format_constraints(DisplayStyle::Mathematical, f, env)
    }

    pub(crate) fn display_quantifiers_and_constraints_math_style<'m>(
        &'m self,
        env: &'m ModuleEnv<'m>,
    ) -> FormatQuantifiersAndConstraintsMathStyle<'m, Self> {
        FormatQuantifiersAndConstraintsMathStyle(FormatWithData {
            value: self,
            data: env,
        })
    }

    pub(crate) fn format_quantifiers_rust_style(
        &self,
        f: &mut std::fmt::Formatter,
    ) -> std::fmt::Result {
        write!(f, "<")?;
        let mut i = 0;
        for quantifier in &self.ty_quantifiers {
            if i > 0 {
                write!(f, ", ")?;
            }
            quantifier.format_rust_style(f)?;
            i += 1;
        }
        for quantifier in self.eff_quantifiers.iter().sorted() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{quantifier}")?;
            i += 1;
        }
        write!(f, ">")
    }

    pub(crate) fn display_quantifiers_rust_style(&self) -> FormatQuantifiersRustStyle<'_, Self> {
        FormatQuantifiersRustStyle(FormatWithData {
            value: self,
            data: &(),
        })
    }

    pub(crate) fn format_constraints_rust_style(
        &self,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv<'_>,
    ) -> std::fmt::Result {
        if self.constraints.is_empty() {
            return Ok(());
        }
        write!(f, "where ")?;
        self.format_constraints(DisplayStyle::Rust, f, env)
    }

    pub(crate) fn display_constraints_rust_style<'m>(
        &'m self,
        env: &'m ModuleEnv<'m>,
    ) -> FormatConstraintsRustStyle<'m, Self> {
        FormatConstraintsRustStyle(FormatWithData {
            value: self,
            data: env,
        })
    }
}

impl<'a, Ty: TypeLike + FormatWith<ModuleEnv<'a>>> TypeScheme<Ty> {
    pub(crate) fn format_math_style(
        &self,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv<'a>,
    ) -> std::fmt::Result {
        self.format_quantifiers_and_constraints_math_style(f, env)?;
        if !self.is_just_type_and_effects() {
            write!(f, " ⇒ ")?;
        }
        write!(f, "{}", self.ty.format_with(env))
    }

    pub fn display_math_style<'m>(&'m self, env: &'m ModuleEnv<'m>) -> FormatMathStyle<'m, Self> {
        FormatMathStyle(FormatWithData {
            value: self,
            data: env,
        })
    }

    pub(crate) fn format_rust_style(
        &self,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv<'a>,
    ) -> std::fmt::Result {
        let has_constraints = !self.constraints.is_empty();
        // if has_constraints {
        //     write!(f, "{{")?;
        // }
        write!(f, "{}", self.ty.format_with(env))?;
        if has_constraints {
            write!(f, " ")?;
            self.format_constraints_rust_style(f, env)?;
            // write!(f, "}}")?;
        }
        Ok(())
    }

    pub fn display_rust_style<'m>(&'m self, env: &'m ModuleEnv<'m>) -> FormatRustStyle<'m, Self> {
        FormatRustStyle(FormatWithData {
            value: self,
            data: env,
        })
    }
}

impl<Ty: TypeLike + Hash> Hash for TypeScheme<Ty> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.ty_quantifiers.hash(state);
        let eff_quantifiers: Vec<_> = self.eff_quantifiers.iter().sorted().collect();
        eff_quantifiers.hash(state);
        self.ty.hash(state);
        self.constraints.hash(state);
    }
}

impl<Ty: TypeLike> TypeLike for TypeScheme<Ty> {
    fn map(&self, f: &mut impl TypeMapper) -> Self {
        let ty = self.ty.map(f);
        let constraints = self.constraints.map(f);
        let ty_quantifiers = Self::list_ty_vars(&ty, constraints.iter());
        let eff_quantifiers = Self::list_eff_vars(&ty, constraints.iter());
        Self {
            ty_quantifiers,
            eff_quantifiers,
            ty,
            constraints,
        }
    }

    fn visit(&self, visitor: &mut impl TypeInnerVisitor) {
        self.ty.visit(visitor);
        self.constraints.visit(visitor);
    }
}

pub fn format_have_trait(
    trait_ref: &TraitRef,
    input_tys: &[Type],
    output_tys: &[Type],
    f: &mut std::fmt::Formatter,
    env: &ModuleEnv<'_>,
) -> std::fmt::Result {
    let trait_name = trait_ref.name;
    if input_tys.len() == 1 {
        write!(f, "{}: {}", input_tys[0].format_with(env), trait_name)?;
        if output_tys.is_empty() {
            return Ok(());
        }
        write!(f, " <")?;
    } else {
        write!(f, "{trait_name} <")?;
        write_with_separator_and_format_fn(
            input_tys.iter().enumerate(),
            ", ",
            |(index, ty), f| {
                write!(
                    f,
                    "{} = {}",
                    trait_ref.input_type_names[index],
                    ty.format_with(env)
                )
            },
            f,
        )?;
    }
    if !output_tys.is_empty() {
        if input_tys.len() != 1 {
            write!(f, " ↦ ")?;
        }
        write_with_separator_and_format_fn(
            output_tys.iter().enumerate(),
            ", ",
            |(index, ty), f| {
                write!(
                    f,
                    "{} = {}",
                    trait_ref.output_type_names[index],
                    ty.format_with(env)
                )
            },
            f,
        )?;
    }
    write!(f, ">")
}

// Build a substitution that maps each type variable to a fresh type variable from 0.
pub(crate) fn normalize_types(tys: &mut [TypeVar]) -> TypeSubstitution {
    let mut ty_subst: std::collections::HashMap<TypeVar, Type> = TypeSubstitution::new();
    tys.iter_mut().enumerate().for_each(|(i, quantifier)| {
        let new_var = TypeVar::new(i as u32);
        ty_subst.insert(*quantifier, Type::variable(new_var));
        *quantifier = new_var;
    });
    ty_subst
}

/// Extra functions parameters that must be passed to resolve polymorphism for a list of constraints.
pub(crate) fn extra_parameters_from_constraints(
    constraints: &[PubTypeConstraint],
) -> ExtraParameters {
    use PubTypeConstraint::*;

    // Build a map from input type variables to their next representation type.
    let mut repr_map_shallow = HashMap::new();
    for constraint in constraints {
        if let HaveTrait {
            trait_ref,
            input_tys,
            output_tys,
            ..
        } = constraint
        {
            if trait_ref == &*REPR_TRAIT {
                let input_ty = input_tys.first().unwrap();
                let output_ty = output_tys.first().unwrap();
                let in_var = input_ty.data().as_variable().copied();
                let out_var = output_ty.data().as_variable().copied();
                if let Some(in_var) = in_var {
                    if let Some(out_var) = out_var {
                        let prev = repr_map_shallow.insert(in_var, out_var);
                        assert!(prev.is_none());
                    }
                }
            }
        }
    }

    // Resolve for each input type variable their deepest representation type.
    let mut repr_map = HashMap::new();
    for (in_var, out_var) in repr_map_shallow.iter() {
        let mut next = *out_var;
        while let Some(next_out_var) = repr_map_shallow.get(&next) {
            next = *next_out_var;
        }
        repr_map.insert(*in_var, next);
    }

    // Process other constraints needing dictionaries.
    let requirements = constraints
        .iter()
        .filter_map(|constraint| match constraint {
            RecordFieldIs {
                record_ty, field, ..
            } => {
                if !record_ty.data().is_variable() {
                    panic!("Type scheme with non-variable record type in constraints")
                }
                Some(DictionaryReq::new_field_index(*record_ty, *field))
            }
            HaveTrait {
                trait_ref,
                input_tys,
                output_tys,
                ..
            } => {
                if input_tys.iter().all(Type::is_constant) {
                    panic!(
                        "Type scheme with trait having only non-variable input types in constraints"
                    )
                }
                if trait_ref == &*REPR_TRAIT {
                    None // Repr is a special marker trait with an empty function dictionary.
                } else {
                    Some(DictionaryReq::new_trait_impl(
                        trait_ref.clone(),
                        input_tys.clone(),
                        output_tys.clone(),
                    ))
                }
            }
            _ => None,
        })
        .collect();

    ExtraParameters {
        requirements,
        repr_map,
    }
}

pub(crate) fn format_constraints(
    constraints: &[PubTypeConstraint],
    style: DisplayStyle,
    f: &mut std::fmt::Formatter,
    env: &ModuleEnv<'_>,
) -> std::fmt::Result {
    use DisplayStyle::*;
    if style == Rust && !constraints.is_empty() {
        return format_constraints_consolidated(constraints, f, env);
    }
    for (i, constraint) in constraints.iter().enumerate() {
        if i > 0 {
            match style {
                Mathematical => write!(f, " ∧ ")?,
                Rust => write!(f, ", ")?,
            }
        }
        match style {
            Mathematical => write!(f, "({})", constraint.format_with(env)),
            Rust => write!(f, "{}", constraint.format_with(env)),
        }?;
    }
    Ok(())
}

pub(crate) fn format_constraints_consolidated(
    constraints: &[PubTypeConstraint],
    f: &mut std::fmt::Formatter,
    env: &ModuleEnv<'_>,
) -> std::fmt::Result {
    let mut first_ty = true;
    // Build aggregated constraints, except for HaveTrait.
    let mut aggregated = BTreeMap::new();
    for constraint in constraints {
        use PubTypeConstraint::*;
        match constraint {
            TupleAtIndexIs {
                tuple_ty,
                index,
                element_ty,
                ..
            } => {
                aggregated
                    .entry(tuple_ty)
                    .or_insert_with(|| AggregatedConstraint::Tuple(TupleConstraint::new()))
                    .as_tuple_mut()
                    .unwrap()
                    .insert(*index, *element_ty);
            }
            RecordFieldIs {
                record_ty,
                field,
                element_ty,
                ..
            } => {
                aggregated
                    .entry(record_ty)
                    .or_insert_with(|| AggregatedConstraint::Record(VariantConstraint::new()))
                    .as_record_mut()
                    .unwrap_or_else(|| {
                        panic!(
                            "Expected record constraint for {}",
                            record_ty.format_with(env)
                        )
                    })
                    .insert(*field, *element_ty);
            }
            TypeHasVariant {
                variant_ty,
                tag,
                payload_ty,
                ..
            } => {
                aggregated
                    .entry(variant_ty)
                    .or_insert_with(|| AggregatedConstraint::Variant(VariantConstraint::new()))
                    .as_variant_mut()
                    .unwrap()
                    .insert(*tag, *payload_ty);
            }
            HaveTrait {
                trait_ref,
                input_tys,
                output_tys,
                ..
            } => {
                if first_ty {
                    first_ty = false;
                } else {
                    f.write_str(", ")?;
                }
                format_have_trait(trait_ref, input_tys, output_tys, f, env)?;
            }
        }
    }
    // Format aggregated constraints.
    for (ty, constraint) in aggregated {
        use AggregatedConstraint::*;
        if first_ty {
            first_ty = false;
        } else {
            f.write_str(", ")?;
        }
        write!(f, "{}: ", ty.format_with(env))?;
        match constraint {
            Tuple(tuple) => {
                f.write_str("(")?;
                let mut last_index = 0;
                for (index, element_ty) in tuple {
                    while last_index < index {
                        write!(f, "_, ")?;
                        last_index += 1;
                    }
                    write!(f, "{}, ", element_ty.format_with(env))?;
                    last_index += 1;
                }
                f.write_str("…)")?;
            }
            Record(record) => {
                f.write_str("{ ")?;
                for (field, element_ty) in record {
                    write!(f, "{}: {}, ", field, element_ty.format_with(env))?;
                }
                f.write_str("… }")?;
            }
            Variant(variant) => {
                for (tag, payload_ty) in variant {
                    if payload_ty == Type::unit() {
                        write!(f, "{tag} | ")?;
                    } else if payload_ty.data().is_tuple() {
                        write!(f, "{} {} | ", tag, payload_ty.format_with(env))?;
                    } else {
                        write!(f, "{} ({}) | ", tag, payload_ty.format_with(env))?;
                    }
                }
                f.write_str("…")?;
            }
        }
    }
    Ok(())
}

pub(crate) struct FormatQuantifiersAndConstraintsMathStyle<'a, T>(
    FormatWithData<'a, T, ModuleEnv<'a>>,
);

impl<Ty: TypeLike> std::fmt::Display
    for FormatQuantifiersAndConstraintsMathStyle<'_, TypeScheme<Ty>>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0
            .value
            .format_quantifiers_and_constraints_math_style(f, self.0.data)
    }
}

pub struct FormatMathStyle<'a, T>(FormatWithData<'a, T, ModuleEnv<'a>>);

impl<'a, Ty: TypeLike + FormatWith<ModuleEnv<'a>>> std::fmt::Display
    for FormatMathStyle<'a, TypeScheme<Ty>>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.value.format_math_style(f, self.0.data)
    }
}

pub(crate) struct FormatQuantifiersRustStyle<'a, T>(FormatWithData<'a, T, ()>);

impl<Ty: TypeLike> std::fmt::Display for FormatQuantifiersRustStyle<'_, TypeScheme<Ty>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.value.format_quantifiers_rust_style(f)
    }
}

pub(crate) struct FormatConstraintsRustStyle<'a, T>(FormatWithData<'a, T, ModuleEnv<'a>>);

impl<Ty: TypeLike> std::fmt::Display for FormatConstraintsRustStyle<'_, TypeScheme<Ty>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.value.format_constraints_rust_style(f, self.0.data)
    }
}

pub struct FormatRustStyle<'a, T>(FormatWithData<'a, T, ModuleEnv<'a>>);

impl<'a, Ty: TypeLike + FormatWith<ModuleEnv<'a>>> std::fmt::Display
    for FormatRustStyle<'a, TypeScheme<Ty>>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.value.format_rust_style(f, self.0.data)
    }
}
