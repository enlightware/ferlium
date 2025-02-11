// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{
    borrow::Borrow,
    collections::{BTreeMap, HashSet},
    hash::{Hash, Hasher},
};

use crate::{
    format::write_with_separator_and_format_fn, location::Span, r#trait::TraitRef, Location,
};
use enum_as_inner::EnumAsInner;
use itertools::Itertools;
use ustr::Ustr;

use crate::{
    dictionary_passing::{instantiate_dictionaries_req, DictionaryReq},
    effects::{EffType, EffectVar, EffectsSubstitution},
    format::FormatWith,
    ir::FnInstData,
    module::{FmtWithModuleEnv, FormatWithModuleEnv, ModuleEnv},
    r#type::{Type, TypeLike, TypeSubstitution, TypeVar},
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
        tuple_span: Location,
        index: usize,
        index_span: Location,
        element_ty: Type,
    },
    /// Record field access constraint: record_ty.field = element_ty
    RecordFieldIs {
        record_ty: Type,
        record_span: Location,
        field: Ustr,
        field_span: Location,
        element_ty: Type,
    },
    /// Variant for type: variant_ty ⊇ tag(payload_ty)
    TypeHasVariant {
        variant_ty: Type,
        variant_span: Location,
        tag: Ustr,
        payload_ty: Type,
        payload_span: Location,
    },
    /// Types have trait
    HaveTrait {
        trait_ref: TraitRef,
        input_tys: Vec<Type>,
        output_tys: Vec<Type>,
        span: Location,
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
            tuple_span,
            index,
            index_span,
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
            record_span,
            field,
            field_span,
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
            variant_span,
            tag,
            payload_ty,
            payload_span,
        }
    }

    pub fn new_have_trait(
        trait_ref: TraitRef,
        input_tys: Vec<Type>,
        output_tys: Vec<Type>,
        span: Location,
    ) -> Self {
        Self::HaveTrait {
            trait_ref,
            input_tys,
            output_tys,
            span,
        }
    }

    pub fn contains_any_ty_vars(&self, vars: &[TypeVar]) -> bool {
        let merge_outputs = |ty: &Type, output: &mut bool| {
            *output = *output || ty.data().contains_any_ty_vars(vars);
        };
        let mut output = false;
        self.fold_ty_in_place(&merge_outputs, &mut output);
        output
    }

    pub fn contains_only_ty_vars(&self, vars: &[TypeVar]) -> bool {
        let merge_outputs = |ty: &Type, output: &mut bool| {
            *output = *output && ty.data().contains_only_ty_vars(vars);
        };
        let mut output = true;
        self.fold_ty_in_place(&merge_outputs, &mut output);
        output
    }

    fn fold_ty_in_place<V>(&self, f: &impl Fn(&Type, &mut V), v: &mut V) {
        use PubTypeConstraint::*;
        match self {
            TupleAtIndexIs {
                tuple_ty,
                element_ty,
                ..
            } => {
                f(tuple_ty, v);
                f(element_ty, v);
            }
            RecordFieldIs {
                record_ty,
                element_ty,
                ..
            } => {
                f(record_ty, v);
                f(element_ty, v);
            }
            TypeHasVariant {
                variant_ty,
                payload_ty,
                ..
            } => {
                f(variant_ty, v);
                f(payload_ty, v);
            }
            HaveTrait {
                input_tys,
                output_tys,
                ..
            } => {
                for ty in input_tys {
                    f(ty, v);
                }
                for ty in output_tys {
                    f(ty, v);
                }
            }
        }
    }

    fn instantiate_module(&mut self, module_name: Option<Ustr>, inst_span: Span) {
        use PubTypeConstraint::*;
        match self {
            TupleAtIndexIs {
                tuple_span,
                index_span,
                ..
            } => {
                tuple_span.instantiate(module_name, inst_span);
                index_span.instantiate(module_name, inst_span);
            }
            RecordFieldIs {
                record_span,
                field_span,
                ..
            } => {
                record_span.instantiate(module_name, inst_span);
                field_span.instantiate(module_name, inst_span);
            }
            TypeHasVariant {
                payload_span: span, ..
            } => {
                span.instantiate(module_name, inst_span);
            }
            HaveTrait { span, .. } => {
                span.instantiate(module_name, inst_span);
            }
        }
    }

    pub fn instantiate_and_drop_if_known_trait(&self, subst: &InstSubstitution) -> Option<Self> {
        let constraint = self.instantiate(subst);
        if constraint.is_have_trait() && constraint.inner_ty_vars().is_empty() {
            None
        } else {
            Some(constraint)
        }
    }
}

impl TypeLike for PubTypeConstraint {
    fn instantiate(&self, subst: &InstSubstitution) -> Self {
        use PubTypeConstraint::*;
        match self {
            TupleAtIndexIs {
                tuple_ty,
                tuple_span,
                index,
                index_span,
                element_ty,
            } => Self::new_tuple_at_index_is(
                tuple_ty.instantiate(subst),
                *tuple_span,
                *index,
                *index_span,
                element_ty.instantiate(subst),
            ),
            RecordFieldIs {
                record_ty,
                record_span,
                field,
                field_span,
                element_ty,
            } => Self::new_record_field_is(
                record_ty.instantiate(subst),
                *record_span,
                *field,
                *field_span,
                element_ty.instantiate(subst),
            ),
            TypeHasVariant {
                variant_ty,
                variant_span,
                tag,
                payload_ty,
                payload_span,
            } => Self::new_type_has_variant(
                variant_ty.instantiate(subst),
                *variant_span,
                *tag,
                payload_ty.instantiate(subst),
                *payload_span,
            ),
            HaveTrait {
                trait_ref,
                input_tys,
                output_tys,
                span,
            } => Self::new_have_trait(
                trait_ref.clone(),
                input_tys.iter().map(|ty| ty.instantiate(subst)).collect(),
                output_tys.iter().map(|ty| ty.instantiate(subst)).collect(),
                *span,
            ),
        }
    }

    fn inner_ty_vars(&self) -> Vec<TypeVar> {
        let extend_vars = |ty: &Type, vars: &mut Vec<TypeVar>| {
            vars.extend(ty.inner_ty_vars());
        };
        let mut vars = Vec::new();
        self.fold_ty_in_place(&extend_vars, &mut vars);
        vars.sort();
        vars.dedup();
        vars
    }

    fn fill_with_input_effect_vars(&self, vars: &mut HashSet<EffectVar>) {
        let extend_vars = |ty: &Type, vars: &mut HashSet<EffectVar>| {
            ty.fill_with_inner_effect_vars(vars);
        };
        self.fold_ty_in_place(&extend_vars, vars);
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
                    tag: v1,
                    payload_ty: p_ty1,
                    ..
                },
                TypeHasVariant {
                    variant_ty: v_ty2,
                    tag: v2,
                    payload_ty: p_ty2,
                    ..
                },
            ) => v_ty1 == v_ty2 && v1 == v2 && p_ty1 == p_ty2,
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
                tag: variant,
                payload_ty,
                ..
            } => {
                variant_ty.hash(state);
                variant.hash(state);
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

impl FmtWithModuleEnv for PubTypeConstraint {
    fn fmt_with_module_env(
        &self,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv<'_>,
    ) -> std::fmt::Result {
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
                tag: variant,
                payload_ty,
                ..
            } => {
                if *payload_ty == Type::unit() {
                    write!(f, "{} ⊇ {}", variant_ty.format_with(env), variant,)
                } else {
                    write!(
                        f,
                        "{} ⊇ {} {}",
                        variant_ty.format_with(env),
                        variant,
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
    pub(crate) ty_quantifiers: Vec<TypeVar>,
    pub(crate) eff_quantifiers: HashSet<EffectVar>,
    pub(crate) ty: Ty,
    pub(crate) constraints: Vec<PubTypeConstraint>,
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
    pub(crate) fn instantiate(
        &self,
        ty_inf: &mut TypeInference,
        src_module_name: Option<Ustr>,
        inst_span: Span,
    ) -> (Ty, FnInstData) {
        let ty_subst = ty_inf.fresh_type_var_subst(&self.ty_quantifiers);
        let eff_subst = ty_inf.fresh_effect_var_subst(&self.eff_quantifiers);
        let subst = (ty_subst, eff_subst);
        for constraint in &self.constraints {
            let mut constraint = constraint.instantiate(&subst);
            constraint.instantiate_module(src_module_name, inst_span);
            ty_inf.add_pub_constraint(constraint);
        }
        let ty = self.ty.instantiate(&subst);
        let dict_req = instantiate_dictionaries_req(&self.extra_parameters(), &subst);
        (ty, FnInstData::new(dict_req))
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

    pub(crate) fn normalize(&mut self) -> InstSubstitution {
        // Build a substitution that maps each type quantifier to a fresh type variable from 0.
        let mut ty_subst = TypeSubstitution::new();
        self.ty_quantifiers
            .iter_mut()
            .enumerate()
            .for_each(|(i, quantifier)| {
                let new_var = TypeVar::new(i as u32);
                ty_subst.insert(*quantifier, Type::variable(new_var));
                *quantifier = new_var;
            });

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

    /// Extra functions parameters that must be passed to resolve polymorphism.
    pub(crate) fn extra_parameters(&self) -> Vec<DictionaryReq> {
        use PubTypeConstraint::*;
        self.constraints
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
                HaveTrait { trait_ref, input_tys, .. } => {
                    if input_tys.iter().all(Type::is_constant) {
                        panic!("Type scheme with trait having only non-variable input types in constraints")
                    }
                    Some(DictionaryReq::new_trait_impl(input_tys.clone(), trait_ref.clone()))
                }
                _ => None,
            })
            .collect()
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
        use DisplayStyle::*;
        if style == Rust && !self.constraints.is_empty() {
            return self.format_constraints_consolidated(f, env);
        }
        for (i, constraint) in self.constraints.iter().enumerate() {
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
        &self,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv<'_>,
    ) -> std::fmt::Result {
        let mut first_ty = true;
        // Build aggregated constraints, except for HaveTrait.
        let mut aggregated = BTreeMap::new();
        for constraint in &self.constraints {
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
                        .unwrap()
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
                            write!(f, "{} | ", tag)?;
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
        FormatQuantifiersAndConstraintsMathStyle(FormatWithModuleEnv {
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

    pub(crate) fn display_quantifiers_rust_style(&self) -> FormatQuantifiersRustStyle<Self> {
        FormatQuantifiersRustStyle(FormatWith {
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
        FormatConstraintsRustStyle(FormatWithModuleEnv {
            value: self,
            data: env,
        })
    }
}

impl<Ty: TypeLike + FmtWithModuleEnv> TypeScheme<Ty> {
    pub(crate) fn format_math_style(
        &self,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv<'_>,
    ) -> std::fmt::Result {
        self.format_quantifiers_and_constraints_math_style(f, env)?;
        if !self.is_just_type_and_effects() {
            write!(f, " ⇒ ")?;
        }
        write!(f, "{}", self.ty.format_with(env))
    }

    pub fn display_math_style<'m>(&'m self, env: &'m ModuleEnv<'m>) -> FormatMathStyle<'m, Self> {
        FormatMathStyle(FormatWithModuleEnv {
            value: self,
            data: env,
        })
    }

    pub(crate) fn format_rust_style(
        &self,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv<'_>,
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
        FormatRustStyle(FormatWithModuleEnv {
            value: self,
            data: env,
        })
    }
}

fn format_have_trait(
    trait_ref: &TraitRef,
    input_tys: &[Type],
    output_tys: &[Type],
    f: &mut std::fmt::Formatter,
    env: &ModuleEnv<'_>,
) -> std::fmt::Result {
    let trait_name = trait_ref.name;
    write!(f, "{} (", trait_name)?;
    write_with_separator_and_format_fn(
        input_tys.iter(),
        ", ",
        |ty, f| write!(f, "{}", ty.format_with(env)),
        f,
    )?;
    if !output_tys.is_empty() {
        write!(f, "; ")?;
        write_with_separator_and_format_fn(
            output_tys.iter(),
            ", ",
            |ty, f| write!(f, "{}", ty.format_with(env)),
            f,
        )?;
    }
    write!(f, ")")
}

pub(crate) struct FormatQuantifiersAndConstraintsMathStyle<'a, T>(FormatWithModuleEnv<'a, T>);

impl<Ty: TypeLike> std::fmt::Display
    for FormatQuantifiersAndConstraintsMathStyle<'_, TypeScheme<Ty>>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0
            .value
            .format_quantifiers_and_constraints_math_style(f, self.0.data)
    }
}

pub struct FormatMathStyle<'a, T>(FormatWithModuleEnv<'a, T>);

impl<Ty: TypeLike + FmtWithModuleEnv> std::fmt::Display for FormatMathStyle<'_, TypeScheme<Ty>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.value.format_math_style(f, self.0.data)
    }
}

pub(crate) struct FormatQuantifiersRustStyle<'a, T>(FormatWith<'a, T, ()>);

impl<Ty: TypeLike> std::fmt::Display for FormatQuantifiersRustStyle<'_, TypeScheme<Ty>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.value.format_quantifiers_rust_style(f)
    }
}

pub(crate) struct FormatConstraintsRustStyle<'a, T>(FormatWithModuleEnv<'a, T>);

impl<Ty: TypeLike> std::fmt::Display for FormatConstraintsRustStyle<'_, TypeScheme<Ty>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.value.format_constraints_rust_style(f, self.0.data)
    }
}

pub struct FormatRustStyle<'a, T>(FormatWithModuleEnv<'a, T>);

impl<Ty: TypeLike + FmtWithModuleEnv> std::fmt::Display for FormatRustStyle<'_, TypeScheme<Ty>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.value.format_rust_style(f, self.0.data)
    }
}
