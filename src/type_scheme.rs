use std::{
    borrow::Borrow,
    collections::{BTreeMap, HashMap},
    hash::{Hash, Hasher},
};

use enum_as_inner::EnumAsInner;
use itertools::Itertools;
use lrpar::Span;
use ustr::Ustr;

use crate::{
    dictionary_passing::{instantiate_dictionaries_req, DictionaryReq},
    ir::FnInstData,
    module::{FmtWithModuleEnv, FormatWithModuleEnv, ModuleEnv},
    r#type::{Type, TypeKind, TypeLike, TypeSubstitution, TypeVar},
    type_inference::TypeInference,
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
        tuple_span: Span,
        index: usize,
        index_span: Span,
        element_ty: Type,
    },
    /// Record field access constraint: record_ty.field = element_ty
    RecordFieldIs {
        record_ty: Type,
        record_span: Span,
        field: Ustr,
        field_span: Span,
        element_ty: Type,
    },
    /// Variant for type: variant_ty ⊇ tag(payload_ty)
    TypeHasVariant {
        variant_ty: Type,
        tag: Ustr,
        payload_ty: Type,
        span: Span,
    },
}

impl PubTypeConstraint {
    pub fn new_tuple_at_index_is(
        tuple_ty: Type,
        tuple_span: Span,
        index: usize,
        index_span: Span,
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
        record_span: Span,
        field: Ustr,
        field_span: Span,
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

    pub fn new_type_has_variant(ty: Type, tag: Ustr, payload_ty: Type, span: Span) -> Self {
        Self::TypeHasVariant {
            variant_ty: ty,
            tag,
            payload_ty,
            span,
        }
    }

    pub fn contains_any_ty_vars(&self, vars: &[TypeVar]) -> bool {
        use PubTypeConstraint::*;
        match self {
            TupleAtIndexIs {
                tuple_ty,
                element_ty,
                ..
            } => {
                tuple_ty.data().contains_any_ty_vars(vars)
                    || element_ty.data().contains_any_ty_vars(vars)
            }
            RecordFieldIs {
                record_ty,
                element_ty,
                ..
            } => {
                record_ty.data().contains_any_ty_vars(vars)
                    || element_ty.data().contains_any_ty_vars(vars)
            }
            TypeHasVariant {
                variant_ty,
                payload_ty,
                ..
            } => {
                variant_ty.data().contains_any_ty_vars(vars)
                    || payload_ty.data().contains_any_ty_vars(vars)
            }
        }
    }

    pub fn contains_only_ty_vars(&self, vars: &[TypeVar]) -> bool {
        use PubTypeConstraint::*;
        match self {
            TupleAtIndexIs {
                tuple_ty,
                element_ty,
                ..
            } => {
                tuple_ty.data().contains_only_ty_vars(vars)
                    && element_ty.data().contains_only_ty_vars(vars)
            }
            RecordFieldIs {
                record_ty,
                element_ty,
                ..
            } => {
                record_ty.data().contains_only_ty_vars(vars)
                    && element_ty.data().contains_only_ty_vars(vars)
            }
            TypeHasVariant {
                variant_ty,
                payload_ty,
                ..
            } => {
                variant_ty.data().contains_only_ty_vars(vars)
                    && payload_ty.data().contains_only_ty_vars(vars)
            }
        }
    }
}

impl TypeLike for PubTypeConstraint {
    fn instantiate(&self, subst: &TypeSubstitution) -> Self {
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
                tag: variant,
                payload_ty,
                span,
            } => Self::new_type_has_variant(
                variant_ty.instantiate(subst),
                *variant,
                payload_ty.instantiate(subst),
                *span,
            ),
        }
    }

    fn inner_ty_vars(&self) -> Vec<TypeVar> {
        use PubTypeConstraint::*;
        match self {
            TupleAtIndexIs {
                tuple_ty,
                element_ty,
                ..
            } => tuple_ty
                .inner_ty_vars()
                .into_iter()
                .chain(element_ty.inner_ty_vars())
                .unique()
                .collect(),
            RecordFieldIs {
                record_ty,
                element_ty,
                ..
            } => record_ty
                .inner_ty_vars()
                .into_iter()
                .chain(element_ty.inner_ty_vars())
                .unique()
                .collect(),
            TypeHasVariant {
                variant_ty,
                payload_ty,
                ..
            } => variant_ty
                .inner_ty_vars()
                .into_iter()
                .chain(payload_ty.inner_ty_vars())
                .unique()
                .collect(),
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
        }
    }
}

/// Aggregated TypeHasVariant or RecordFieldIs constraints to be use for checking and display.
pub type VariantConstraint = BTreeMap<Ustr, Type>;
/// Aggregated TupleAtIndexIs constraints to be use for checking and display.
pub type TupleConstraint = BTreeMap<usize, Type>;

#[derive(EnumAsInner)]
enum AggregatedConstraint {
    Tuple(TupleConstraint),
    Record(VariantConstraint),
    Variant(VariantConstraint),
}

/// A type, with quantified type variables and associated constraints.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeScheme<Ty: TypeLike> {
    // for a compiled module, quantifiers should be equalt to the type variables in the type
    // and the constraints.
    pub(crate) quantifiers: Vec<TypeVar>,
    pub(crate) ty: Ty,
    pub(crate) constraints: Vec<PubTypeConstraint>,
}

impl<Ty: TypeLike> TypeScheme<Ty> {
    /// Create a new type scheme with no quantifier nor constraints.
    pub(crate) fn new_just_type(ty: Ty) -> Self {
        Self {
            quantifiers: vec![],
            ty,
            constraints: vec![],
        }
    }

    /// Create a new type scheme by inferring quantifiers from the type, and no constraints.
    pub(crate) fn new_infer_quantifiers(ty: Ty) -> Self {
        let quantifiers = ty.inner_ty_vars();
        Self {
            quantifiers,
            ty,
            constraints: vec![],
        }
    }

    /// Return the quantifiers of this type scheme.
    pub(crate) fn quantifiers_from_signature(&self) -> Vec<TypeVar> {
        Self::list_ty_vars(&self.ty, self.constraints.iter())
    }

    /// Returns whether there are no quantifiers nor constraints.
    pub fn is_just_type(&self) -> bool {
        self.quantifiers.is_empty() && self.constraints.is_empty()
    }

    /// Instantiate this type scheme with fresh type variables in ty_inf.
    pub(crate) fn instantiate(&self, ty_inf: &mut TypeInference) -> (Ty, FnInstData) {
        let subst = ty_inf.fresh_type_var_subs(&self.quantifiers);
        for constraint in &self.constraints {
            ty_inf.add_pub_constraint(constraint.instantiate(&subst));
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
            .sorted()
            .collect()
    }

    pub(crate) fn normalize(&mut self) -> TypeSubstitution {
        // Build a substitution that maps each quantifier to a fresh type variable from 0.
        let mut var_subst = TypeSubstitution::new();
        self.quantifiers
            .iter_mut()
            .enumerate()
            .for_each(|(i, quantifier)| {
                let new_var = TypeVar::new(i as u32);
                var_subst.insert(*quantifier, Type::variable(new_var));
                *quantifier = new_var;
            });
        // Apply to type and constraints
        self.ty = self.ty.instantiate(&var_subst);
        self.constraints = self
            .constraints
            .iter()
            .map(|constraint| constraint.instantiate(&var_subst))
            .collect();
        // Return
        var_subst
    }

    /// Extra functions parameters that must be passed to resolve polymorphism.
    pub(crate) fn extra_parameters(&self) -> Vec<DictionaryReq<TypeVar>> {
        self.constraints
            .iter()
            .filter_map(|constraint| {
                if let PubTypeConstraint::RecordFieldIs {
                    record_ty, field, ..
                } = constraint
                {
                    if let TypeKind::Variable(var) = *record_ty.data() {
                        Some(DictionaryReq::new_field_index(var, *field))
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .collect()
    }

    pub(crate) fn format_quantifiers(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        for (i, quantifier) in self.quantifiers.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "∀{}", quantifier)?;
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
        // Build aggregated constraints.
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
            }
        }
        // Format aggregated constraints.
        let mut first_ty = true;
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
                    }
                    f.write_str("…)")?;
                }
                Record(record) => {
                    f.write_str("{ ")?;
                    let mut first = true;
                    for (field, element_ty) in record {
                        write!(f, "{}: {}, ", field, element_ty.format_with(env))?;
                    }
                    f.write_str("… }")?;
                }
                Variant(variant) => {
                    for (tag, payload_ty) in variant {
                        if payload_ty == Type::unit() {
                            write!(f, "{} | ", tag)?;
                        } else {
                            write!(f, "{} {} | ", tag, payload_ty.format_with(env))?;
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
        self.format_quantifiers(f)?;
        if !self.quantifiers.is_empty() {
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
        if !self.is_just_type() {
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

pub(crate) struct FormatQuantifiersAndConstraintsMathStyle<'a, T>(FormatWithModuleEnv<'a, T>);

impl<'m, Ty: TypeLike> std::fmt::Display
    for FormatQuantifiersAndConstraintsMathStyle<'m, TypeScheme<Ty>>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0
            .value
            .format_quantifiers_and_constraints_math_style(f, self.0.data)
    }
}

pub struct FormatMathStyle<'a, T>(FormatWithModuleEnv<'a, T>);

impl<'m, Ty: TypeLike + FmtWithModuleEnv> std::fmt::Display
    for FormatMathStyle<'m, TypeScheme<Ty>>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.value.format_math_style(f, self.0.data)
    }
}

pub(crate) struct FormatConstraintsRustStyle<'a, T>(FormatWithModuleEnv<'a, T>);

impl<'m, Ty: TypeLike> std::fmt::Display for FormatConstraintsRustStyle<'m, TypeScheme<Ty>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.value.format_constraints_rust_style(f, self.0.data)
    }
}

pub struct FormatRustStyle<'a, T>(FormatWithModuleEnv<'a, T>);

impl<'m, Ty: TypeLike + FmtWithModuleEnv> std::fmt::Display
    for FormatRustStyle<'m, TypeScheme<Ty>>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.value.format_rust_style(f, self.0.data)
    }
}
