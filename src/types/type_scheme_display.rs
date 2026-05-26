// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::collections::BTreeMap;

use crate::{FxHashMap, FxHashSet};

use enum_as_inner::EnumAsInner;
use itertools::Itertools;

use crate::{
    format::{FormatWith, FormatWithData, write_with_separator_and_format_fn},
    module::ModuleEnv,
    std::value::VALUE_TRAIT,
    types::{
        effects::EffectsInstSubst,
        r#trait::TraitRef,
        r#type::{Type, TypeDisplayEnv, TypeInstSubst, TypeVar},
        type_inference::substitution::InstSubst,
        type_like::TypeLike,
        type_scheme::{PubTypeConstraint, TupleConstraint, TypeScheme, VariantConstraint},
    },
};

impl FormatWith<ModuleEnv<'_>> for PubTypeConstraint {
    fn fmt_with(&self, f: &mut std::fmt::Formatter, env: &ModuleEnv<'_>) -> std::fmt::Result {
        format_pub_type_constraint(self, f, env)
    }
}

impl FormatWith<TypeDisplayEnv<'_, '_>> for PubTypeConstraint {
    fn fmt_with(
        &self,
        f: &mut std::fmt::Formatter,
        env: &TypeDisplayEnv<'_, '_>,
    ) -> std::fmt::Result {
        format_pub_type_constraint(self, f, env)
    }
}

#[derive(Clone, Copy)]
pub(crate) enum TypeConstraintRenderStyle {
    WhereClause,
    ParentList,
}

#[derive(Clone, Copy)]
pub(crate) enum TypeSchemeConstraintRenderMode {
    Full,
    Light,
}

fn format_pub_type_constraint<Env>(
    constraint: &PubTypeConstraint,
    f: &mut std::fmt::Formatter,
    env: &Env,
) -> std::fmt::Result
where
    Type: FormatWith<Env>,
{
    format_pub_type_constraint_with_style(
        constraint,
        f,
        env,
        TypeConstraintRenderStyle::WhereClause,
    )
}

pub(crate) fn format_pub_type_constraint_with_style<Env>(
    constraint: &PubTypeConstraint,
    f: &mut std::fmt::Formatter,
    env: &Env,
    style: TypeConstraintRenderStyle,
) -> std::fmt::Result
where
    Type: FormatWith<Env>,
{
    use PubTypeConstraint::*;
    match constraint {
        TupleAtIndexIs {
            tuple_ty,
            index,
            element_ty,
            ..
        } => write!(
            f,
            "{}.{} = {}",
            tuple_ty.format_with(env),
            index,
            element_ty.format_with(env)
        ),
        RecordFieldIs {
            record_ty,
            field,
            element_ty,
            ..
        } => write!(
            f,
            "{}.{} = {}",
            record_ty.format_with(env),
            field,
            element_ty.format_with(env)
        ),
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
        } => format_have_trait_with_env(trait_ref, input_tys, output_tys, f, env, style),
    }
}

/// Aggregated constraint for display.
#[derive(Clone, EnumAsInner)]
enum AggregatedConstraint {
    Tuple(TupleConstraint),
    Record(VariantConstraint),
    Variant(VariantConstraint),
}

fn collect_aggregated_constraint(
    aggregated: &mut BTreeMap<Type, AggregatedConstraint>,
    constraint: &PubTypeConstraint,
) {
    use PubTypeConstraint::*;
    match constraint {
        TupleAtIndexIs {
            tuple_ty,
            index,
            element_ty,
            ..
        } => {
            aggregated
                .entry(*tuple_ty)
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
                .entry(*record_ty)
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
                .entry(*variant_ty)
                .or_insert_with(|| AggregatedConstraint::Variant(VariantConstraint::new()))
                .as_variant_mut()
                .unwrap()
                .insert(*tag, *payload_ty);
        }
        HaveTrait { .. } => {}
    }
}

fn write_constraint_separator(f: &mut std::fmt::Formatter, first: &mut bool) -> std::fmt::Result {
    if *first {
        *first = false;
    } else {
        f.write_str(", ")?;
    }
    Ok(())
}

fn write_aggregated_constraint<Env>(
    ty: Type,
    constraint: AggregatedConstraint,
    f: &mut std::fmt::Formatter,
    env: &Env,
) -> std::fmt::Result
where
    Type: FormatWith<Env>,
{
    write!(f, "{}: ", ty.format_with(env))?;
    match constraint {
        AggregatedConstraint::Tuple(tuple) => {
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
        AggregatedConstraint::Record(record) => {
            f.write_str("{ ")?;
            for (field, element_ty) in record {
                write!(f, "{}: {}, ", field, element_ty.format_with(env))?;
            }
            f.write_str("… }")?;
        }
        AggregatedConstraint::Variant(variant) => {
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
    Ok(())
}

#[derive(Default)]
struct DisplayConstraints<'a> {
    simple_trait_constraints: FxHashMap<Type, Vec<&'a TraitRef>>,
    other_trait_constraints: Vec<NonUnaryTraitConstraint<'a>>,
    structural_constraints: BTreeMap<Type, AggregatedConstraint>,
}

#[derive(Clone, Copy)]
struct NonUnaryTraitConstraint<'a> {
    trait_ref: &'a TraitRef,
    input_tys: &'a [Type],
    output_tys: &'a [Type],
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
struct ConstraintSortKey {
    category: u8,
    primary_rank: u32,
    primary_ty: String,
    secondary: String,
}

enum ConstraintDisplayItem<'a> {
    UnaryTraitGroup {
        input_ty: Type,
        trait_refs: Vec<&'a TraitRef>,
    },
    NonUnaryTraitConstraint(NonUnaryTraitConstraint<'a>),
    StructuralConstraint {
        ty: Type,
        constraint: AggregatedConstraint,
    },
}

impl<'a> DisplayConstraints<'a> {
    fn full(constraints: &'a [PubTypeConstraint]) -> Self {
        let mut display_constraints = Self::default();
        for constraint in constraints {
            display_constraints.push(constraint);
        }
        display_constraints
    }

    fn light(constraints: &'a [PubTypeConstraint]) -> Self {
        let parent_constraints = transitive_parent_constraints(constraints);
        let mut display_constraints = Self::default();
        for constraint in constraints {
            if is_hidden_light_constraint(constraint) || parent_constraints.contains(constraint) {
                continue;
            }
            display_constraints.push(constraint);
        }
        display_constraints
    }

    fn push(&mut self, constraint: &'a PubTypeConstraint) {
        match constraint {
            PubTypeConstraint::HaveTrait {
                trait_ref,
                input_tys,
                output_tys,
                ..
            } if input_tys.len() == 1 && output_tys.is_empty() => {
                self.simple_trait_constraints
                    .entry(input_tys[0])
                    .or_default()
                    .push(trait_ref);
            }
            PubTypeConstraint::HaveTrait {
                trait_ref,
                input_tys,
                output_tys,
                ..
            } => {
                self.other_trait_constraints.push(NonUnaryTraitConstraint {
                    trait_ref,
                    input_tys,
                    output_tys,
                });
            }
            PubTypeConstraint::TupleAtIndexIs { .. }
            | PubTypeConstraint::RecordFieldIs { .. }
            | PubTypeConstraint::TypeHasVariant { .. } => {
                collect_aggregated_constraint(&mut self.structural_constraints, constraint);
            }
        }
    }

    fn is_empty(&self) -> bool {
        self.simple_trait_constraints.is_empty()
            && self.other_trait_constraints.is_empty()
            && self.structural_constraints.is_empty()
    }

    fn format<Env>(&self, f: &mut std::fmt::Formatter, env: &Env) -> std::fmt::Result
    where
        Type: FormatWith<Env>,
    {
        let mut items = self
            .simple_trait_constraints
            .iter()
            .map(|(ty, trait_refs)| {
                let mut trait_refs = trait_refs.clone();
                trait_refs.sort_by_key(|trait_ref| trait_ref.name);
                trait_refs.dedup_by_key(|trait_ref| trait_ref.name);
                ConstraintDisplayItem::UnaryTraitGroup {
                    input_ty: *ty,
                    trait_refs,
                }
            })
            .collect::<Vec<_>>();
        items.extend(
            self.other_trait_constraints
                .iter()
                .copied()
                .map(ConstraintDisplayItem::NonUnaryTraitConstraint),
        );
        items.extend(self.structural_constraints.iter().map(|(ty, constraint)| {
            ConstraintDisplayItem::StructuralConstraint {
                ty: *ty,
                constraint: constraint.clone(),
            }
        }));
        items.sort_by_key(|item| item.sort_key(env));

        let mut first = true;
        for item in items {
            write_constraint_separator(f, &mut first)?;
            item.format(f, env)?;
        }

        Ok(())
    }
}

impl ConstraintDisplayItem<'_> {
    fn sort_key<Env>(&self, env: &Env) -> ConstraintSortKey
    where
        Type: FormatWith<Env>,
    {
        match self {
            Self::UnaryTraitGroup {
                input_ty,
                trait_refs,
            } => constraint_sort_key(
                0,
                Some(*input_ty),
                trait_refs
                    .iter()
                    .map(|trait_ref| trait_ref.name.as_str())
                    .join(" + "),
                env,
            ),
            Self::NonUnaryTraitConstraint(constraint) => constraint_sort_key(
                0,
                constraint.input_tys.first().copied(),
                constraint.trait_ref.name.to_string(),
                env,
            ),
            Self::StructuralConstraint { ty, constraint } => constraint_sort_key(
                1,
                Some(*ty),
                aggregated_constraint_sort_name(constraint),
                env,
            ),
        }
    }

    fn format<Env>(&self, f: &mut std::fmt::Formatter, env: &Env) -> std::fmt::Result
    where
        Type: FormatWith<Env>,
    {
        match self {
            Self::UnaryTraitGroup {
                input_ty,
                trait_refs,
            } => {
                write!(f, "{}: ", input_ty.format_with(env))?;
                write_with_separator_and_format_fn(
                    trait_refs,
                    " + ",
                    |trait_ref, f| write!(f, "{}", trait_ref.name),
                    f,
                )
            }
            Self::NonUnaryTraitConstraint(constraint) => format_have_trait_with_env(
                constraint.trait_ref,
                constraint.input_tys,
                constraint.output_tys,
                f,
                env,
                TypeConstraintRenderStyle::WhereClause,
            ),
            Self::StructuralConstraint { ty, constraint } => {
                write_aggregated_constraint(*ty, constraint.clone(), f, env)
            }
        }
    }
}

fn is_hidden_light_constraint(constraint: &PubTypeConstraint) -> bool {
    matches!(
        constraint,
        PubTypeConstraint::HaveTrait {
            trait_ref,
            input_tys,
            output_tys,
            ..
        } if trait_ref == &*VALUE_TRAIT && input_tys.len() == 1 && output_tys.is_empty()
    )
}

fn transitive_parent_constraints(
    constraints: &[PubTypeConstraint],
) -> FxHashSet<PubTypeConstraint> {
    let mut parent_constraints = FxHashSet::default();
    for constraint in constraints {
        collect_transitive_parent_constraints(constraint, &mut parent_constraints);
    }
    parent_constraints
}

fn collect_transitive_parent_constraints(
    constraint: &PubTypeConstraint,
    parent_constraints: &mut FxHashSet<PubTypeConstraint>,
) {
    let PubTypeConstraint::HaveTrait {
        trait_ref,
        input_tys,
        output_tys,
        ..
    } = constraint
    else {
        return;
    };
    let subst = trait_constraint_subst(trait_ref, input_tys, output_tys);
    for parent_constraint in &trait_ref.parent_constraints {
        let parent_constraint = parent_constraint.instantiate_simple(&subst);
        if parent_constraints.insert(parent_constraint.clone()) {
            collect_transitive_parent_constraints(&parent_constraint, parent_constraints);
        }
    }
}

fn trait_constraint_subst(
    trait_ref: &TraitRef,
    input_tys: &[Type],
    output_tys: &[Type],
) -> InstSubst {
    let mut ty_subst = TypeInstSubst::default();
    for (index, ty) in input_tys.iter().enumerate() {
        ty_subst.insert(TypeVar::new(index as u32), *ty);
    }
    let input_ty_count = trait_ref.input_type_count();
    for (index, ty) in output_tys.iter().enumerate() {
        ty_subst.insert(TypeVar::new(input_ty_count + index as u32), *ty);
    }
    (ty_subst, EffectsInstSubst::default())
}

fn constraint_sort_key<Env>(
    category: u8,
    primary_ty: Option<Type>,
    secondary: String,
    env: &Env,
) -> ConstraintSortKey
where
    Type: FormatWith<Env>,
{
    let (primary_rank, primary_ty) = match primary_ty {
        Some(ty) => match ty.data().as_variable().copied() {
            Some(var) => (var.name(), ty.format_with(env).to_string()),
            None => (u32::MAX, ty.format_with(env).to_string()),
        },
        None => (u32::MAX, String::new()),
    };
    ConstraintSortKey {
        category,
        primary_rank,
        primary_ty,
        secondary,
    }
}

fn aggregated_constraint_sort_name(constraint: &AggregatedConstraint) -> String {
    match constraint {
        AggregatedConstraint::Tuple(_) => "tuple".to_string(),
        AggregatedConstraint::Record(_) => "record".to_string(),
        AggregatedConstraint::Variant(_) => "variant".to_string(),
    }
}

impl<Ty: TypeLike> TypeScheme<Ty> {
    pub(crate) fn format_constraints_with_type_env(
        &self,
        f: &mut std::fmt::Formatter,
        env: &TypeDisplayEnv<'_, '_>,
    ) -> std::fmt::Result {
        self.format_constraints_with_mode(f, env, TypeSchemeConstraintRenderMode::Full)
    }

    pub(crate) fn format_constraints_with_mode(
        &self,
        f: &mut std::fmt::Formatter,
        env: &TypeDisplayEnv<'_, '_>,
        mode: TypeSchemeConstraintRenderMode,
    ) -> std::fmt::Result {
        let constraints = match mode {
            TypeSchemeConstraintRenderMode::Full => DisplayConstraints::full(&self.constraints),
            TypeSchemeConstraintRenderMode::Light => DisplayConstraints::light(&self.constraints),
        };
        if constraints.is_empty() {
            return Ok(());
        }
        write!(f, "where ")?;
        constraints.format(f, env)
    }

    pub(crate) fn display_constraints_with_type_env<'a, 'm>(
        &'a self,
        env: &'a TypeDisplayEnv<'a, 'm>,
    ) -> DisplayConstraintsWithTypeEnv<'a, 'm, Ty> {
        self.display_constraints_with_mode(env, TypeSchemeConstraintRenderMode::Full)
    }

    pub(crate) fn display_constraints_with_mode<'a, 'm>(
        &'a self,
        env: &'a TypeDisplayEnv<'a, 'm>,
        mode: TypeSchemeConstraintRenderMode,
    ) -> DisplayConstraintsWithTypeEnv<'a, 'm, Ty> {
        DisplayConstraintsWithTypeEnv {
            value: self,
            env,
            mode,
        }
    }
}

impl<'a, Ty> TypeScheme<Ty>
where
    Ty: TypeLike + FormatWith<ModuleEnv<'a>>,
    Ty: for<'b, 'm> FormatWith<TypeDisplayEnv<'b, 'm>>,
{
    pub(crate) fn format_with_module_env(
        &self,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv<'a>,
    ) -> std::fmt::Result {
        let has_constraints = !self.constraints.is_empty();
        let ty_var_names = self.display_ty_var_names();
        let type_env = self.type_display_env(env, &ty_var_names);
        write!(f, "{}", self.ty.format_with(&type_env))?;
        if has_constraints {
            write!(f, " ")?;
            write!(f, "where ")?;
            format_constraints_consolidated_with_env(&self.constraints, f, &type_env)?;
        }
        Ok(())
    }

    pub fn display<'m>(&'m self, env: &'m ModuleEnv<'m>) -> DisplayTypeScheme<'m, Self> {
        DisplayTypeScheme(FormatWithData {
            value: self,
            data: env,
        })
    }
}

pub fn format_have_trait(
    trait_ref: &TraitRef,
    input_tys: &[Type],
    output_tys: &[Type],
    f: &mut std::fmt::Formatter,
    env: &ModuleEnv<'_>,
) -> std::fmt::Result {
    format_have_trait_with_env(
        trait_ref,
        input_tys,
        output_tys,
        f,
        env,
        TypeConstraintRenderStyle::WhereClause,
    )
}

fn format_have_trait_with_env<Env>(
    trait_ref: &TraitRef,
    input_tys: &[Type],
    output_tys: &[Type],
    f: &mut std::fmt::Formatter,
    env: &Env,
    style: TypeConstraintRenderStyle,
) -> std::fmt::Result
where
    Type: FormatWith<Env>,
{
    let trait_name = trait_ref.name;
    let use_unary_where_clause =
        input_tys.len() == 1 && matches!(style, TypeConstraintRenderStyle::WhereClause);
    if use_unary_where_clause {
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
        if !use_unary_where_clause {
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

pub(crate) fn format_constraints_consolidated(
    constraints: &[PubTypeConstraint],
    f: &mut std::fmt::Formatter,
    env: &ModuleEnv<'_>,
) -> std::fmt::Result {
    format_constraints_consolidated_with_env(constraints, f, env)
}

fn format_constraints_consolidated_with_env<Env>(
    constraints: &[PubTypeConstraint],
    f: &mut std::fmt::Formatter,
    env: &Env,
) -> std::fmt::Result
where
    Type: FormatWith<Env>,
{
    DisplayConstraints::full(constraints).format(f, env)
}

pub(crate) struct DisplayConstraintsWithTypeEnv<'a, 'm, T: TypeLike> {
    value: &'a TypeScheme<T>,
    env: &'a TypeDisplayEnv<'a, 'm>,
    mode: TypeSchemeConstraintRenderMode,
}

impl<Ty: TypeLike> std::fmt::Display for DisplayConstraintsWithTypeEnv<'_, '_, Ty> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.value
            .format_constraints_with_mode(f, self.env, self.mode)
    }
}

pub struct DisplayTypeScheme<'a, T>(FormatWithData<'a, T, ModuleEnv<'a>>);

impl<'a, Ty> std::fmt::Display for DisplayTypeScheme<'a, TypeScheme<Ty>>
where
    Ty: TypeLike + FormatWith<ModuleEnv<'a>>,
    Ty: for<'b, 'm> FormatWith<TypeDisplayEnv<'b, 'm>>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.value.format_with_module_env(f, self.0.data)
    }
}
