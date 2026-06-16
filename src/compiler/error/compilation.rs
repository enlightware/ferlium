// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{
    fmt::{self, Debug, Display},
    ops::Deref,
};

use crate::{
    ast,
    containers::iterable_to_string,
    format::{FormatWith, write_with_separator, write_with_separator_and_format_fn},
    module::{ModuleId, TraitId, TypeDefId},
    parser::location::{Location, SourceTable},
    types::type_inference::unify::SubOrSameType,
    types::type_scheme::PubTypeConstraint,
};
use enum_as_inner::EnumAsInner;
use itertools::Itertools;
use ustr::Ustr;

use super::resolve_must_be_mutable_ctx;

use crate::{
    ast::{PatternType, PropertyAccess},
    module::ModuleEnv,
    types::effects::{EffType, EffectVar},
    types::r#type::{Type, TypeVar},
};

pub type LocatedError = (String, Location);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ADTAccessType {
    RecordAccess,
    TupleProject,
    Variant,
}
impl ADTAccessType {
    pub fn adt_kind(&self) -> &'static str {
        use ADTAccessType::*;
        match self {
            RecordAccess => "record",
            TupleProject => "tuple",
            Variant => "variant",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MutabilityMustBeWhat {
    Mutable,
    Constant,
    Equal,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MutabilityMustBeContext {
    Value,
    FnTypeArg(usize),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DuplicatedFieldContext {
    Record,
    Struct,
}
impl DuplicatedFieldContext {
    pub fn as_str(&self) -> &'static str {
        use DuplicatedFieldContext::*;
        match self {
            Record => "record",
            Struct => "struct",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DuplicatedVariantContext {
    Match,
    Enum,
    Variant,
}
impl DuplicatedVariantContext {
    pub fn as_str(&self) -> &'static str {
        use DuplicatedVariantContext::*;
        match self {
            Match => "match",
            Enum => "enum",
            Variant => "variant union",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WhichProductTypeIsNot {
    Unit,
    Record,
    Tuple,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WhatIsNotAProductType {
    EnumVariant(Ustr),
    Struct,
}
impl WhatIsNotAProductType {
    pub fn from_tag(tag: Option<Ustr>) -> Self {
        tag.map_or(Self::Struct, Self::EnumVariant)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GenericParamsOwner {
    TypeDef { name: Ustr },
    TypeAlias { name: Ustr },
    Function { name: Ustr },
    Trait { name: Ustr },
    TraitImpl { trait_name: Ustr },
}

impl GenericParamsOwner {
    pub fn description(&self) -> String {
        match self {
            Self::TypeDef { name } => format!("type definition `{name}`"),
            Self::TypeAlias { name } => format!("type alias `{name}`"),
            Self::Function { name } => format!("function `{name}`"),
            Self::Trait { name } => format!("trait `{name}`"),
            Self::TraitImpl { trait_name } => format!("impl of trait `{trait_name}`"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InvalidGenericParamsKind {
    DuplicateParam { name: Ustr },
    DuplicateEffectParam { name: Ustr },
}

impl InvalidGenericParamsKind {
    pub fn message(&self, owner: GenericParamsOwner) -> String {
        match self {
            Self::DuplicateParam { name } => {
                format!(
                    "Duplicate generic type parameter `{name}` in {}",
                    owner.description()
                )
            }
            Self::DuplicateEffectParam { name } => {
                format!(
                    "Duplicate generic effect parameter `{name}` in {}",
                    owner.description()
                )
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InvalidTraitConstraintKind {
    UnknownInputBinding {
        name: Ustr,
    },
    DuplicateInputBinding {
        name: Ustr,
    },
    MissingInputBindings {
        names: Vec<Ustr>,
    },
    UnknownOutputBinding {
        name: Ustr,
    },
    DuplicateOutputBinding {
        name: Ustr,
    },
    MissingOutputBindings {
        names: Vec<Ustr>,
    },
    UnknownOutputEffectBinding {
        name: Ustr,
    },
    DuplicateOutputEffectBinding {
        name: Ustr,
    },
    MissingOutputEffectBindings {
        names: Vec<Ustr>,
    },
    ExpectedNamedInputs {
        expected_count: usize,
    },
    WrongNumberOfInputBindings {
        expected_count: usize,
        got_count: usize,
    },
}

impl InvalidTraitConstraintKind {
    pub fn message(&self, trait_name: &str) -> String {
        use InvalidTraitConstraintKind::*;
        match self {
            UnknownInputBinding { name } => {
                format!("Unknown input type parameter `{name}` for trait `{trait_name}`")
            }
            DuplicateInputBinding { name } => {
                format!("Duplicate input type parameter `{name}` for trait `{trait_name}`")
            }
            MissingInputBindings { names } => format!(
                "Missing input type parameters {} for trait `{trait_name}`",
                iterable_to_string(names, ", ")
            ),
            UnknownOutputBinding { name } => {
                format!("Unknown output type parameter `{name}` for trait `{trait_name}`")
            }
            DuplicateOutputBinding { name } => {
                format!("Duplicate output type parameter `{name}` for trait `{trait_name}`")
            }
            MissingOutputBindings { names } => format!(
                "Missing output type parameters {} for trait `{trait_name}`",
                iterable_to_string(names, ", ")
            ),
            UnknownOutputEffectBinding { name } => {
                format!("Unknown output effect parameter `{name}` for trait `{trait_name}`")
            }
            DuplicateOutputEffectBinding { name } => {
                format!("Duplicate output effect parameter `{name}` for trait `{trait_name}`")
            }
            MissingOutputEffectBindings { names } => format!(
                "Missing output effect parameters {} for trait `{trait_name}`",
                iterable_to_string(names, ", ")
            ),
            ExpectedNamedInputs { expected_count } => format!(
                "Trait `{trait_name}` expects {expected_count} named input type parameters in this constraint"
            ),
            WrongNumberOfInputBindings {
                expected_count,
                got_count,
            } => format!(
                "Trait `{trait_name}` expects {expected_count} input type parameters in this constraint, got {got_count}"
            ),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InvalidTraitDefinitionKind {
    MissingInputTypes,
    InvalidConstraintTypeVar {
        ty_var: TypeVar,
    },
    MissingInputTypeVarInMethod {
        method_name: Ustr,
        ty_var: TypeVar,
    },
    UnreachableConstraintInputTypeVar {
        method_name: Ustr,
        constraint_index: usize,
    },
}

impl InvalidTraitDefinitionKind {
    pub fn message(&self, trait_name: Ustr) -> String {
        use InvalidTraitDefinitionKind::*;
        match self {
            MissingInputTypes => {
                format!("Trait `{trait_name}` must have at least one input type parameter")
            }
            InvalidConstraintTypeVar { ty_var } => format!(
                "Trait `{trait_name}` refers to invalid type variable `{ty_var}` in its where clause"
            ),
            MissingInputTypeVarInMethod {
                method_name,
                ty_var,
            } => format!(
                "Trait method `{trait_name}::{method_name}` must mention input type variable `{ty_var}` in its signature"
            ),
            UnreachableConstraintInputTypeVar {
                method_name,
                constraint_index,
            } => format!(
                "Trait method `{trait_name}::{method_name}` cannot use where-clause constraint #{} because its input types are not reachable from the method signature or earlier constraints",
                constraint_index + 1
            ),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnsupportedTraitDefinitionKind {
    GenericMethod {
        method_name: Ustr,
        quantifier: TypeVar,
    },
    GenericEffect {
        method_name: Ustr,
        effect_vars: Vec<EffectVar>,
    },
    GenericConstraints {
        method_name: Ustr,
        constraint_count: usize,
    },
}

impl UnsupportedTraitDefinitionKind {
    pub fn message(&self, trait_name: Ustr) -> String {
        use UnsupportedTraitDefinitionKind::*;
        match self {
            GenericMethod {
                method_name,
                quantifier,
            } => format!(
                "Generic trait methods are not supported yet, but `{trait_name}::{method_name}` quantifies over `{quantifier}`"
            ),
            GenericEffect {
                method_name,
                effect_vars,
            } => format!(
                "Generic effects in trait methods are not supported yet, but `{trait_name}::{method_name}` uses effect variables {}",
                iterable_to_string(effect_vars, ", ")
            ),
            GenericConstraints {
                method_name,
                constraint_count,
            } => format!(
                "Generic constraints in trait methods are not supported yet, but `{trait_name}::{method_name}` has {constraint_count} generic constraints"
            ),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InvalidTraitAssociatedConstImplKind {
    Unknown { name: Ustr },
    Duplicate { name: Ustr },
    Missing { names: Vec<Ustr> },
}

impl InvalidTraitAssociatedConstImplKind {
    pub fn message(&self, trait_name: &str) -> String {
        use InvalidTraitAssociatedConstImplKind::*;
        match self {
            Unknown { name } => {
                format!("Associated const `{name}` is not part of trait `{trait_name}`")
            }
            Duplicate { name } => {
                format!(
                    "Associated const `{name}` is implemented more than once for trait `{trait_name}`"
                )
            }
            Missing { names } => format!(
                "Implementation of trait `{trait_name}` is missing associated consts `{}`",
                names.iter().join(", ")
            ),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InvalidEnumDefaultAttributeKind {
    MultipleDefaultVariants {
        first_variant: Ustr,
        second_variant: Ustr,
    },
}

impl InvalidEnumDefaultAttributeKind {
    pub fn message(&self, type_name: Ustr) -> String {
        match self {
            Self::MultipleDefaultVariants {
                first_variant,
                second_variant,
            } => format!(
                "Enum `{type_name}` has multiple variants marked with `#[default]`: `{first_variant}` and `{second_variant}`"
            ),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AttributeTarget {
    Function { name: Ustr },
    TypeDef { name: Ustr },
    EnumVariant { type_name: Ustr, variant_name: Ustr },
}

impl AttributeTarget {
    fn message(&self) -> String {
        match self {
            Self::Function { name } => format!("function `{name}`"),
            Self::TypeDef { name } => format!("type definition `{name}`"),
            Self::EnumVariant {
                type_name,
                variant_name,
            } => format!("enum variant `{type_name}::{variant_name}`"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InvalidAttributeKind {
    HasArguments,
    Duplicate,
}

impl InvalidAttributeKind {
    pub fn message(&self, attribute_name: Ustr, target: &AttributeTarget) -> String {
        let target = target.message();
        match self {
            Self::HasArguments => {
                format!("Attribute `#[{attribute_name}]` does not accept arguments on {target}")
            }
            Self::Duplicate => {
                format!("{target} declares `#[{attribute_name}]` more than once")
            }
        }
    }
}

/// A scope of error messages, either internal within the compiler, or external for users.
pub trait Scope: Sized {
    type Type: Debug + Clone;
    type TypeVar: Debug + Clone;
    type TypeDefId: Debug + Clone;
    type PubTypeConstraint: Debug + Clone;
    type TraitName: Debug + Clone;
    type TraitImplHeader: Debug + Clone;
    type ValidVariant: Debug + Clone;
}

#[derive(Debug, Clone)]
pub struct InternalTraitImplHeader {
    pub input_tys: Vec<Type>,
    pub output_tys: Vec<Type>,
    pub ty_var_count: u32,
    pub constraints: Vec<PubTypeConstraint>,
    pub module_id: Option<ModuleId>,
}

#[derive(Debug, Clone)]
pub struct ExternalTraitImplHeader {
    pub input_bindings: Vec<(String, String)>,
    pub output_bindings: Vec<(String, String)>,
    pub ty_var_count: u32,
    pub constraints: Vec<String>,
    pub module_name: Option<String>,
}

pub struct DisplayTraitImplHeader<'a> {
    trait_name: &'a str,
    header: &'a ExternalTraitImplHeader,
}

impl ExternalTraitImplHeader {
    pub fn display<'a>(&'a self, trait_name: &'a str) -> DisplayTraitImplHeader<'a> {
        DisplayTraitImplHeader {
            trait_name,
            header: self,
        }
    }
}

impl Display for DisplayTraitImplHeader<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let header = self.header;
        write!(f, "impl")?;
        if header.ty_var_count > 0 {
            write!(f, "<")?;
            write_with_separator((0..header.ty_var_count).map(TypeVar::new), ", ", f)?;
            write!(f, ">")?;
        }
        if header.input_bindings.len() == 1 && header.output_bindings.is_empty() {
            write!(f, " {} for {}", self.trait_name, header.input_bindings[0].1)?;
        } else {
            write!(f, " {} for <", self.trait_name)?;
            write_with_separator_and_format_fn(
                header.input_bindings.iter(),
                ", ",
                |(name, ty), f| write!(f, "{name} = {ty}"),
                f,
            )?;
            if !header.output_bindings.is_empty() {
                write!(f, " |-> ")?;
                write_with_separator_and_format_fn(
                    header.output_bindings.iter(),
                    ", ",
                    |(name, ty), f| write!(f, "{name} = {ty}"),
                    f,
                )?;
            }
            write!(f, ">")?;
        }
        if !header.constraints.is_empty() {
            write!(f, " where ")?;
            write_with_separator(header.constraints.iter(), ", ", f)?;
        }
        if let Some(module_name) = &header.module_name {
            write!(f, " in module {module_name}")?;
        }
        Ok(())
    }
}

/// Internal scope, using internal compiler representations.
/// Types are complete internal types.
#[derive(Debug, Clone)]
pub struct Internal;
impl Scope for Internal {
    type Type = Type;
    type TypeVar = TypeVar;
    type TypeDefId = TypeDefId;
    type PubTypeConstraint = PubTypeConstraint;
    type TraitName = TraitId;
    type TraitImplHeader = InternalTraitImplHeader;
    type ValidVariant = ();
}

/// External scope, using user-facing representations.
/// Types are strings suitable for display.
#[derive(Debug, Clone)]
pub struct External;
impl Scope for External {
    type Type = String;
    type TypeVar = String;
    type TypeDefId = (String, Location);
    type PubTypeConstraint = String;
    type TraitName = String;
    type TraitImplHeader = ExternalTraitImplHeader;
    type ValidVariant = Vec<String>;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, EnumAsInner)]
pub enum ImportKind {
    // TODO: split between introduced_name and original_symbol once we support "as" renaming
    Symbol(Ustr),
    Module,
}

/// An import site within a module.
#[derive(Debug, Clone)]
pub struct ImportSite {
    pub kind: ImportKind,
    pub module: crate::module::path::Path,
    pub span: Location,
}

/// Compilation error implementation.
/// Uses the tree-that-grows pattern to be generic over
/// the scope of error message use.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnsafeFeature {
    EffectsUnsafe,
    Function(Ustr),
    TypeAlias(Ustr),
    FunctionAttribute(Ustr),
    TypeAttribute(Ustr),
}

impl Display for UnsafeFeature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UnsafeFeature::EffectsUnsafe => write!(f, "`effects_unsafe`"),
            UnsafeFeature::Function(name) => write!(f, "function `{name}`"),
            UnsafeFeature::TypeAlias(name) => write!(f, "type alias `{name}`"),
            UnsafeFeature::FunctionAttribute(name) => write!(f, "function attribute `#[{name}]`"),
            UnsafeFeature::TypeAttribute(name) => write!(f, "type attribute `#[{name}]`"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoopControlKind {
    Break,
    Continue,
}

impl Display for LoopControlKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Break => write!(f, "break"),
            Self::Continue => write!(f, "continue"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InvalidLoopControlKind {
    OutsideLoop,
    UnknownLabel { label: Ustr },
}

impl InvalidLoopControlKind {
    pub fn message(&self, control: LoopControlKind) -> String {
        match self {
            Self::OutsideLoop => format!("{control} can only be used inside a loop"),
            Self::UnknownLabel { label } => {
                format!("{control} targets unknown loop label `{label}`")
            }
        }
    }
}

#[derive(Debug, Clone, EnumAsInner)]
pub enum InfiniteTypeKind<S: Scope> {
    TypeVariableCycle { ty_var: S::TypeVar, ty: S::Type },
    TypeVariableSumCycleWithoutTerminatingVariant { ty_var: S::TypeVar, ty: S::Type },
    ProductCycleWithoutSum { name: Ustr },
    SumCycleWithoutTerminatingVariant { name: Ustr },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InvalidRecursiveTypeKind {
    NonRegularGenericShape { name: Ustr },
}

impl InvalidRecursiveTypeKind {
    pub fn message(&self) -> String {
        match self {
            Self::NonRegularGenericShape { name } => format!(
                "Recursive generic type `{name}` is non-regular; recursive references must use the type parameters unchanged"
            ),
        }
    }
}

#[derive(Debug, Clone, EnumAsInner)]
pub enum CompilationErrorImpl<S: Scope> {
    ParsingFailed(Vec<LocatedError>),
    NameDefinedMultipleTimes {
        name: Ustr,
        first_occurrence: Location,
        second_occurrence: Location,
    },
    NameImportedMultipleTimes {
        name: Ustr,
        occurrences: Vec<ImportSite>,
    },
    ImportConflictsWithLocalDefinition {
        name: Ustr,
        definition_span: Location,
        import_site: ImportSite,
    },
    ImportNotFound(ImportSite),
    TypeNotFound(Location),
    EffectNotFound {
        name: Ustr,
        span: Location,
    },
    TraitNotFound(Location),
    InvalidGenericParams {
        owner: GenericParamsOwner,
        kind: InvalidGenericParamsKind,
        span: Location,
    },
    InvalidTraitConstraint {
        trait_name: String,
        kind: InvalidTraitConstraintKind,
        span: Location,
    },
    InvalidTraitDefinition {
        trait_name: Ustr,
        kind: InvalidTraitDefinitionKind,
        span: Location,
    },
    UnsupportedTraitDefinition {
        trait_name: Ustr,
        kind: UnsupportedTraitDefinitionKind,
        span: Location,
    },
    InvalidEnumDefaultAttribute {
        type_name: Ustr,
        kind: InvalidEnumDefaultAttributeKind,
        span: Location,
    },
    InvalidAttribute {
        attribute_name: Ustr,
        target: AttributeTarget,
        kind: InvalidAttributeKind,
        span: Location,
    },
    WrongNumberOfArguments {
        expected: usize,
        expected_span: Location,
        got: usize,
        got_span: Location,
    },
    MutabilityMustBe {
        source_span: Location,
        reason_span: Location,
        what: MutabilityMustBeWhat,
        ctx: MutabilityMustBeContext,
    },
    TypeMismatch {
        current_ty: S::Type,
        current_span: Location,
        expected_ty: S::Type,
        expected_span: Location,
        sub_or_same: SubOrSameType,
    },
    NamedTypeMismatch {
        current_decl: S::TypeDefId,
        current_span: Location,
        expected_decl: S::TypeDefId,
        expected_span: Location,
    },
    PrivateReprAccess {
        type_def: S::TypeDefId,
        access_span: Location,
    },
    InfiniteType {
        kind: InfiniteTypeKind<S>,
        span: Location,
    },
    InvalidRecursiveType {
        kind: InvalidRecursiveTypeKind,
        span: Location,
    },
    UnboundTypeVar {
        ty_var: S::TypeVar,
        ty: S::Type,
        span: Location,
    },
    UnresolvedConstraints {
        constraints: Vec<S::PubTypeConstraint>,
        span: Location,
    },
    InvalidTupleIndex {
        index: usize,
        index_span: Location,
        tuple_length: usize,
        tuple_span: Location,
    },
    InvalidTupleProjection {
        expr_ty: S::Type,
        expr_span: Location,
        index_span: Location,
    },
    DuplicatedField {
        first_occurrence: Location,
        second_occurrence: Location,
        constructor_span: Location,
        ctx: DuplicatedFieldContext,
    },
    InvalidRecordField {
        field_span: Location,
        record_ty: S::Type,
        record_span: Location,
    },
    InvalidRecordFieldAccess {
        field_span: Location,
        record_ty: S::Type,
        record_span: Location,
    },
    InvalidVariantName {
        name: Location,
        ty: S::Type,
        valid: S::ValidVariant,
    },
    InvalidVariantType {
        name: Location,
        ty: S::Type,
    },
    InvalidVariantConstructor {
        span: Location,
        // The constructor path does not resolve to an enum variant.
    },
    IsNotCorrectProductType {
        which: WhichProductTypeIsNot,
        type_def: S::TypeDefId,
        what: WhatIsNotAProductType,
        instantiation_span: Location,
    },
    InvalidStructField {
        type_def: S::TypeDefId,
        field_name: Ustr,
        field_span: Location,
        instantiation_span: Location,
    },
    MissingStructField {
        type_def: S::TypeDefId,
        field_name: Ustr,
        instantiation_span: Location,
    },
    InconsistentADT {
        a_type: ADTAccessType,
        a_span: Location,
        b_type: ADTAccessType,
        b_span: Location,
    },
    EmptyMatchBody {
        span: Location,
    },
    InconsistentPattern {
        a_type: PatternType,
        a_span: Location,
        b_type: PatternType,
        b_span: Location,
    },
    DuplicatedVariant {
        first_occurrence: Location,
        second_occurrence: Location,
        ctx_span: Location,
        ctx: DuplicatedVariantContext,
    },
    VariantNameConflictsWithType {
        name: Ustr,
        span: Location,
    },
    RecordWildcardPatternNotAtEnd {
        pattern_span: Location,
        wildcard_span: Location,
    },
    TraitImplNotFound {
        trait_ref: S::TraitName,
        input_tys: Vec<S::Type>,
        fn_span: Location,
    },
    TraitSolverRecursionLimitExceeded {
        trait_ref: S::TraitName,
        input_tys: Vec<S::Type>,
        fn_span: Location,
    },
    TraitSolverCycleDetected {
        trait_ref: S::TraitName,
        input_tys: Vec<S::Type>,
        fn_span: Location,
    },
    MethodsNotPartOfTrait {
        trait_ref: S::TraitName,
        spans: Vec<Location>,
    },
    TraitMethodImplsMissing {
        trait_ref: S::TraitName,
        impl_span: Location,
        missings: Vec<Ustr>,
    },
    InvalidTraitAssociatedConstImpl {
        trait_ref: S::TraitName,
        kind: InvalidTraitAssociatedConstImplKind,
        span: Location,
    },
    TraitImplOrphanRuleViolation {
        trait_ref: S::TraitName,
        input_tys: Vec<S::Type>,
        impl_span: Location,
    },
    TraitImplForAnonymousStructuralType {
        input_ty: S::Type,
        impl_span: Location,
    },
    TraitImplNativeOnly {
        trait_ref: S::TraitName,
        impl_span: Location,
    },
    OverlappingTraitImpls {
        trait_ref: S::TraitName,
        input_tys: Vec<S::Type>,
        impl_span: Location,
        existing_impl: S::TraitImplHeader,
        existing_span: Option<Location>,
    },
    TraitMethodArgCountMismatch {
        trait_ref: S::TraitName,
        method_index: usize,
        method_name: Ustr,
        expected: usize,
        got: usize,
        args_span: Location,
    },
    TraitMethodEffectMismatch {
        trait_ref: S::TraitName,
        method_name: Ustr,
        expected: EffType,
        got: EffType,
        span: Location,
    },
    CompilerOnlyTraitMethodUse {
        trait_ref: S::TraitName,
        method_name: Ustr,
        span: Location,
    },
    UnsafeFeatureUseNotAllowed {
        feature: UnsafeFeature,
        span: Location,
    },
    InvalidLoopControl {
        control: LoopControlKind,
        kind: InvalidLoopControlKind,
        span: Location,
    },
    IdentifierBoundMoreThanOnceInAPattern {
        first_occurrence: Location,
        second_occurrence: Location,
        pattern_span: Location,
    },
    DuplicatedLiteralPattern {
        first_occurrence: Location,
        second_occurrence: Location,
        match_span: Location,
    },
    NonExhaustivePattern {
        span: Location,
        ty: S::Type,
        // TODO: have a generic way to talk about the non-covered values
    },
    TypeValuesCannotBeEnumerated {
        span: Location,
        ty: S::Type,
    },
    MutablePathsOverlap {
        a_span: Location,
        b_span: Location,
        fn_span: Location,
    },
    UndefinedVarInStringFormatting {
        var_span: Location,
        string_span: Location,
    },
    InvalidEffectDependency {
        source: EffType,
        source_span: Location,
        target: EffType,
        target_span: Location,
    },
    UnknownProperty {
        scope: ast::Path,
        variable: Ustr,
        cause: PropertyAccess,
        span: Location,
    },
    Unsupported {
        span: Location,
        reason: String,
    },
    ReturnOutsideFunction {
        span: Location,
    },
    /*UnresolvedImport {
        function_path: String,
        span: Location,
    },
    ImportSignatureMismatch {
        function_path: String,
        expected_signature: String,
        got_signature: String,
        span: Location,
    },*/
    CircularImportDependency {
        origin: String,
        import_chain: Vec<String>,
        span: Location,
    },
    Internal {
        span: Location,
        error: String,
    },
}

#[derive(Debug, Clone)]
pub struct BoxedCompilationError<S: Scope>(Box<CompilationErrorImpl<S>>);
impl<S: Scope> BoxedCompilationError<S> {
    pub fn new(error: CompilationErrorImpl<S>) -> Self {
        Self(Box::new(error))
    }
    pub fn into_inner(self) -> CompilationErrorImpl<S> {
        *self.0
    }
}

impl<S: Scope> Deref for BoxedCompilationError<S> {
    type Target = CompilationErrorImpl<S>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

pub type InternalCompilationError = BoxedCompilationError<Internal>;

#[macro_export]
macro_rules! internal_compilation_error {
    ($($ctor:tt)*) => {
        InternalCompilationError::new(
            $crate::compiler::error::CompilationErrorImpl::$($ctor)*
        )
    };
}

impl InternalCompilationError {
    pub fn new_unsafe_feature_use_not_allowed(feature: UnsafeFeature, span: Location) -> Self {
        internal_compilation_error!(UnsafeFeatureUseNotAllowed { feature, span })
    }

    pub fn new_inconsistent_adt(
        mut a_type: ADTAccessType,
        mut a_span: Location,
        mut b_type: ADTAccessType,
        mut b_span: Location,
    ) -> Self {
        if a_span.start() > b_span.start() {
            std::mem::swap(&mut a_type, &mut b_type);
            std::mem::swap(&mut a_span, &mut b_span);
        }
        internal_compilation_error!(InconsistentADT {
            a_type,
            a_span,
            b_type,
            b_span,
        })
    }
}

impl FormatWith<(ModuleEnv<'_>, &SourceTable)> for InternalCompilationError {
    fn fmt_with(
        &self,
        f: &mut fmt::Formatter<'_>,
        data: &(ModuleEnv<'_>, &SourceTable),
    ) -> fmt::Result {
        let (env, source_table) = data;
        let error = CompilationError::resolve_types(self.clone(), env, source_table);
        write!(f, "{}", error.format_with(*source_table))
    }
}

fn span_to_string(loc: &Location, source_table: &SourceTable) -> String {
    let start = loc.start_usize();
    let end = loc.end_usize();
    let source_id = loc.source_id();
    match source_table.get_source_entry(source_id) {
        Some(entry) => {
            let position = entry.get_line_column(start);
            let snippet = entry.get_snippet(start, end);
            let source_name = entry.name();
            format!(
                "`{}` (in {}:{}:{})",
                snippet, source_name, position.0, position.1,
            )
        }
        None => {
            format!("#{}:{}..{}", source_id, start, end)
        }
    }
}

fn external_trait_impl_header_from_internal(
    header: InternalTraitImplHeader,
    trait_ref: TraitId,
    env: &ModuleEnv<'_>,
) -> ExternalTraitImplHeader {
    let trait_def = env.trait_def(trait_ref);
    ExternalTraitImplHeader {
        input_bindings: header
            .input_tys
            .iter()
            .zip(trait_def.input_type_names.iter())
            .map(|(ty, name)| (name.to_string(), ty.format_with(env).to_string()))
            .collect(),
        output_bindings: header
            .output_tys
            .iter()
            .zip(trait_def.output_type_names.iter())
            .map(|(ty, name)| (name.to_string(), ty.format_with(env).to_string()))
            .collect(),
        ty_var_count: header.ty_var_count,
        constraints: header
            .constraints
            .iter()
            .map(|constraint| constraint.format_with(env).to_string())
            .collect(),
        module_name: header
            .module_id
            .and_then(|module_id| env.modules.get_name(module_id).map(ToString::to_string)),
    }
}

fn type_def_origin_from_internal(
    type_def: TypeDefId,
    fallback_span: Location,
    env: &ModuleEnv<'_>,
) -> <External as Scope>::TypeDefId {
    let span = env.try_type_def_span(type_def).unwrap_or(fallback_span);
    (type_def.format_with(env).to_string(), span)
}

pub type CompilationError = BoxedCompilationError<External>;

impl FormatWith<SourceTable> for CompilationError {
    fn fmt_with(&self, f: &mut fmt::Formatter<'_>, data: &SourceTable) -> fmt::Result {
        let fmt_span = |loc: &Location| span_to_string(loc, data);
        use CompilationErrorImpl::*;
        match self.deref() {
            ParsingFailed(errors) => {
                write!(f, "Parsing failed: ")?;
                for (i, (msg, span)) in errors.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{} in {}", msg, fmt_span(span))?;
                }
                Ok(())
            }
            NameDefinedMultipleTimes { name, .. } => {
                write!(f, "Name `{name}` defined multiple times")
            }
            NameImportedMultipleTimes { name, .. } => {
                write!(f, "Name `{name}` imported multiple times")
            }
            ImportConflictsWithLocalDefinition {
                name, import_site, ..
            } => {
                write!(
                    f,
                    "Name `{name}` imported from `{}` conflicts with local definition",
                    import_site.module
                )
            }
            ImportNotFound(site) => match &site.kind {
                ImportKind::Symbol(symbol) => write!(
                    f,
                    "Import of `{}` not found in module `{}`",
                    symbol, site.module
                ),
                ImportKind::Module => write!(f, "Module {} does not exist", site.module),
            },
            TypeNotFound(span) => {
                write!(f, "Cannot find type {} in this scope", fmt_span(span))
            }
            EffectNotFound { name, span } => {
                write!(f, "Cannot find effect `{name}` in {}", fmt_span(span))
            }
            TraitNotFound(span) => {
                write!(f, "Cannot find trait {} in this scope", fmt_span(span))
            }
            InvalidGenericParams { owner, kind, span } => {
                write!(f, "{} in {}", kind.message(*owner), fmt_span(span))
            }
            InvalidTraitConstraint {
                trait_name,
                kind,
                span,
            } => {
                write!(f, "{} in {}", kind.message(trait_name), fmt_span(span))
            }
            InvalidTraitDefinition {
                trait_name,
                kind,
                span,
            } => {
                write!(f, "{} in {}", kind.message(*trait_name), fmt_span(span))
            }
            UnsupportedTraitDefinition {
                trait_name,
                kind,
                span,
            } => {
                write!(f, "{} in {}", kind.message(*trait_name), fmt_span(span))
            }
            InvalidEnumDefaultAttribute {
                type_name,
                kind,
                span,
            } => {
                write!(f, "{} in {}", kind.message(*type_name), fmt_span(span))
            }
            InvalidAttribute {
                attribute_name,
                target,
                kind,
                span,
            } => {
                write!(
                    f,
                    "{} in {}",
                    kind.message(*attribute_name, target),
                    fmt_span(span)
                )
            }
            WrongNumberOfArguments {
                expected,
                expected_span,
                got,
                got_span,
            } => {
                write!(
                    f,
                    "Wrong number of arguments: expected {} due to {}, but {} were provided in {}",
                    expected,
                    fmt_span(expected_span),
                    got,
                    fmt_span(got_span)
                )
            }
            MutabilityMustBe {
                source_span,
                reason_span,
                what,
                ..
            } => {
                let source_name = fmt_span(source_span);
                let reason_name = fmt_span(reason_span);
                use MutabilityMustBeWhat::*;
                let what = match what {
                    Mutable => "mutable due to",
                    Constant => "constant due to",
                    Equal => "of same mutability to",
                };
                write!(f, "Expression {source_name} must be {what} {reason_name}")
            }
            TypeMismatch {
                current_ty,
                current_span,
                expected_ty,
                expected_span,
                sub_or_same,
            } => write!(
                f,
                "Type `{}` in {} is not {} `{}` in {}",
                current_ty,
                fmt_span(current_span),
                match sub_or_same {
                    SubOrSameType::SubType => "a sub-type of",
                    SubOrSameType::SameTypeWithSubEffects => "the same type as",
                },
                expected_ty,
                fmt_span(expected_span),
            ),
            NamedTypeMismatch {
                current_decl,
                current_span,
                expected_decl,
                expected_span,
            } => write!(
                f,
                "Named type `{}` in {} (from {}) is different than named type `{}` in {} (from {})",
                current_decl.0,
                fmt_span(current_span),
                fmt_span(&current_decl.1),
                expected_decl.0,
                fmt_span(expected_span),
                fmt_span(&expected_decl.1),
            ),
            PrivateReprAccess {
                type_def,
                access_span,
            } => write!(
                f,
                "Representation of `{}` is private and cannot be accessed in {}",
                type_def.0,
                fmt_span(access_span)
            ),
            InfiniteType { kind, span } => match kind {
                InfiniteTypeKind::TypeVariableCycle { ty_var, ty } => {
                    write!(
                        f,
                        "Infinite type: `{}` = `{}` in {}",
                        ty_var,
                        ty,
                        fmt_span(span)
                    )
                }
                InfiniteTypeKind::TypeVariableSumCycleWithoutTerminatingVariant { ty_var, ty } => {
                    write!(
                        f,
                        "Infinite type: `{}` = `{}` because every variant branch refers back to the recursive cycle in {}",
                        ty_var,
                        ty,
                        fmt_span(span)
                    )
                }
                InfiniteTypeKind::ProductCycleWithoutSum { name } => {
                    write!(
                        f,
                        "Type `{name}` is infinitely recursive because its cycle does not pass through an enum or variant union in {}",
                        fmt_span(span)
                    )
                }
                InfiniteTypeKind::SumCycleWithoutTerminatingVariant { name } => {
                    write!(
                        f,
                        "Type `{name}` is infinitely recursive because every enum or variant-union branch refers back to the recursive cycle in {}",
                        fmt_span(span)
                    )
                }
            },
            InvalidRecursiveType { kind, span } => {
                write!(f, "{} in {}", kind.message(), fmt_span(span))
            }
            UnboundTypeVar { ty_var, ty, span } => {
                write!(
                    f,
                    "Unbound type variable `{}` in type `{}` in {}",
                    ty_var,
                    ty,
                    fmt_span(span)
                )
            }
            UnresolvedConstraints { constraints, span } => {
                write!(
                    f,
                    "Unresolved constraints `{}` in expression {}",
                    constraints.join(" ∧ "),
                    fmt_span(span)
                )
            }
            InvalidTupleIndex {
                index,
                tuple_length,
                tuple_span,
                ..
            } => {
                write!(
                    f,
                    "Invalid index {} of a tuple of length {} in {}",
                    index,
                    tuple_length,
                    fmt_span(tuple_span)
                )
            }
            InvalidTupleProjection {
                expr_ty, expr_span, ..
            } => {
                write!(
                    f,
                    "Expected tuple, got `{}` in {}",
                    expr_ty,
                    fmt_span(expr_span)
                )
            }
            DuplicatedField {
                first_occurrence,
                constructor_span,
                ctx,
                ..
            } => {
                write!(
                    f,
                    "Duplicated field {} in {} {}",
                    fmt_span(first_occurrence),
                    ctx.as_str(),
                    fmt_span(constructor_span)
                )
            }
            InvalidRecordField {
                field_span,
                record_ty,
                record_span,
            } => {
                write!(
                    f,
                    "Field {} not found in record {} of type `{}`",
                    fmt_span(field_span),
                    fmt_span(record_span),
                    record_ty,
                )
            }
            InvalidRecordFieldAccess {
                field_span,
                record_ty,
                record_span,
            } => {
                write!(
                    f,
                    "Expected record due to {}, got `{}` in {}",
                    fmt_span(field_span),
                    record_ty,
                    fmt_span(record_span)
                )
            }
            InvalidVariantName { name, ty, valid } => {
                write!(
                    f,
                    "Variant name {} does not exist for variant type `{}`, valid names are `{}`",
                    fmt_span(name),
                    ty,
                    valid.join(", ")
                )
            }
            InvalidVariantType { name, ty } => {
                write!(
                    f,
                    "Type `{}` is not a variant, but variant constructor {} requires it",
                    ty,
                    fmt_span(name)
                )
            }
            InvalidVariantConstructor { span } => {
                write!(f, "Invalid variant constructor path {}", fmt_span(span))
            }
            ReturnOutsideFunction { span } => {
                write!(
                    f,
                    "Return statement can only be used inside a function, but found in sub-expression {}",
                    fmt_span(span)
                )
            }
            IsNotCorrectProductType {
                which,
                type_def,
                what,
                instantiation_span,
            } => {
                use WhichProductTypeIsNot::*;
                let which = match which {
                    Unit => "arguments, but none are provided in",
                    Record => "a record, but none is provided in",
                    Tuple => "a tuple, but none is provided in",
                };
                let what = match what {
                    WhatIsNotAProductType::EnumVariant(tag) => {
                        format!("Variant `{tag}` of `{}`", type_def.0)
                    }
                    WhatIsNotAProductType::Struct => format!("`{}`", type_def.0),
                };
                write!(
                    f,
                    "{} requires {} {}",
                    what,
                    which,
                    fmt_span(instantiation_span)
                )
            }
            InvalidStructField {
                type_def,
                instantiation_span,
                field_name,
                ..
            } => {
                write!(
                    f,
                    "Field `{}` does not exists in `{}`, but is present in {}",
                    field_name,
                    type_def.0,
                    fmt_span(instantiation_span)
                )
            }
            MissingStructField {
                type_def,
                field_name,
                instantiation_span,
            } => {
                write!(
                    f,
                    "Field `{}` from `{}` is missing in {}",
                    field_name,
                    type_def.0,
                    fmt_span(instantiation_span)
                )
            }
            InconsistentADT {
                a_type,
                a_span,
                b_type,
                b_span,
            } => {
                write!(
                    f,
                    "Inconsistent data types: {} due to {} is incompatible with {} due to {}",
                    a_type.adt_kind(),
                    fmt_span(a_span),
                    b_type.adt_kind(),
                    fmt_span(b_span)
                )
            }
            InconsistentPattern {
                a_type,
                a_span,
                b_type,
                b_span,
            } => {
                write!(
                    f,
                    "Inconsistent pattern types: {} due to `{}` is incompatible with {} due to `{}`",
                    a_type.name(),
                    fmt_span(a_span),
                    b_type.name(),
                    fmt_span(b_span)
                )
            }
            DuplicatedVariant {
                first_occurrence,
                ctx_span,
                ctx,
                ..
            } => {
                write!(
                    f,
                    "Duplicated variant {} in {} {}",
                    fmt_span(first_occurrence),
                    ctx.as_str(),
                    fmt_span(ctx_span)
                )
            }
            VariantNameConflictsWithType { name, span } => {
                write!(
                    f,
                    "Variant name `{name}` conflicts with a type name in {}",
                    fmt_span(span)
                )
            }
            RecordWildcardPatternNotAtEnd { pattern_span, .. } => {
                write!(
                    f,
                    "Record wildcard pattern .. must be at the end of the pattern in {}",
                    fmt_span(pattern_span)
                )
            }
            TraitImplNotFound {
                trait_ref,
                input_tys,
                fn_span,
            } => {
                write!(
                    f,
                    "Implementation of trait `{}` over types `{}` not found (when calling {})",
                    trait_ref,
                    input_tys.join(", "),
                    fmt_span(fn_span)
                )
            }
            TraitSolverRecursionLimitExceeded {
                trait_ref,
                input_tys,
                fn_span,
            } => {
                write!(
                    f,
                    "Recursion limit exceeded while solving trait implementation for `{}` over types `{}` (at {})",
                    trait_ref,
                    input_tys.join(", "),
                    fmt_span(fn_span)
                )
            }
            TraitSolverCycleDetected {
                trait_ref,
                input_tys,
                fn_span,
            } => {
                write!(
                    f,
                    "Cycle detected while solving trait implementation for `{}` over types `{}` (at {})",
                    trait_ref,
                    input_tys.join(", "),
                    fmt_span(fn_span)
                )
            }
            MethodsNotPartOfTrait { trait_ref, spans } => {
                write!(
                    f,
                    "Methods {} are not part of trait `{}`",
                    spans.iter().map(fmt_span).join(", "),
                    trait_ref
                )
            }
            TraitMethodImplsMissing {
                trait_ref,
                missings,
                impl_span,
            } => {
                write!(
                    f,
                    "Implementation of trait `{}` is missing methods `{}` in {}",
                    trait_ref,
                    missings.iter().join(", "),
                    fmt_span(impl_span)
                )
            }
            InvalidTraitAssociatedConstImpl {
                trait_ref,
                kind,
                span,
            } => {
                write!(f, "{} in {}", kind.message(trait_ref), fmt_span(span))
            }
            TraitImplOrphanRuleViolation {
                trait_ref,
                input_tys,
                impl_span,
            } => {
                write!(
                    f,
                    "Implementation of foreign trait `{}` over types `{}` violates the orphan rule in {}",
                    trait_ref,
                    input_tys.join(", "),
                    fmt_span(impl_span)
                )
            }
            TraitImplForAnonymousStructuralType {
                input_ty,
                impl_span,
            } => {
                write!(
                    f,
                    "Trait implementations for anonymous structural type `{}` are not allowed in {}; define a named type and implement the trait for it instead",
                    input_ty,
                    fmt_span(impl_span)
                )
            }
            TraitImplNativeOnly {
                trait_ref,
                impl_span,
            } => {
                write!(
                    f,
                    "Trait `{}` can only be implemented by trusted native code (at {})",
                    trait_ref,
                    fmt_span(impl_span)
                )
            }
            OverlappingTraitImpls {
                trait_ref,
                input_tys,
                impl_span,
                existing_impl,
                ..
            } => {
                write!(
                    f,
                    "Implementation of trait `{}` over types `{}` overlaps with existing impl `{}` in {}",
                    trait_ref,
                    input_tys.join(", "),
                    existing_impl.display(trait_ref),
                    fmt_span(impl_span)
                )
            }
            TraitMethodArgCountMismatch {
                trait_ref,
                method_name,
                expected,
                got,
                args_span,
                ..
            } => {
                write!(
                    f,
                    "Method `{}` of trait `{}` expects {} arguments, but {} are provided in {}",
                    method_name,
                    trait_ref,
                    expected,
                    got,
                    fmt_span(args_span)
                )
            }
            TraitMethodEffectMismatch {
                trait_ref,
                method_name,
                expected,
                got,
                span,
            } => {
                write!(
                    f,
                    "Method `{}` of trait `{}` has effects `{}`, but implementation has effects `{}` in {}",
                    method_name,
                    trait_ref,
                    if expected.is_empty() {
                        "none".to_string()
                    } else {
                        expected.to_string()
                    },
                    if got.is_empty() {
                        "none".to_string()
                    } else {
                        got.to_string()
                    },
                    fmt_span(span)
                )
            }
            CompilerOnlyTraitMethodUse {
                trait_ref,
                method_name,
                span,
            } => {
                write!(
                    f,
                    "Method `{}::{}` is compiler-only and cannot be used in Ferlium source in {}",
                    trait_ref,
                    method_name,
                    fmt_span(span)
                )
            }
            UnsafeFeatureUseNotAllowed { feature, span } => {
                write!(
                    f,
                    "Unsafe feature {} cannot be used in this context in {}",
                    feature,
                    fmt_span(span)
                )
            }
            InvalidLoopControl {
                control,
                kind,
                span,
            } => {
                write!(f, "{} in {}", kind.message(*control), fmt_span(span))
            }
            IdentifierBoundMoreThanOnceInAPattern {
                first_occurrence,
                pattern_span,
                ..
            } => {
                write!(
                    f,
                    "Identifier {} bound more than once in a pattern: {}",
                    fmt_span(first_occurrence),
                    fmt_span(pattern_span)
                )
            }
            DuplicatedLiteralPattern {
                first_occurrence,
                match_span,
                ..
            } => {
                write!(
                    f,
                    "Duplicated literal pattern {} in match {}",
                    fmt_span(first_occurrence),
                    fmt_span(match_span)
                )
            }
            EmptyMatchBody { span } => {
                write!(f, "Match body cannot be empty in {}", fmt_span(span))
            }
            NonExhaustivePattern { span, ty } => {
                write!(
                    f,
                    "Non-exhaustive patterns for type `{}`, all possible values must be covered in {}",
                    ty,
                    fmt_span(span)
                )
            }
            TypeValuesCannotBeEnumerated { span, ty } => {
                write!(
                    f,
                    "Values of type `{}` cannot be enumerated in {}, but all possible values must be known for exhaustive match coverage analysis",
                    ty,
                    fmt_span(span)
                )
            }
            MutablePathsOverlap {
                a_span,
                b_span,
                fn_span,
            } => {
                write!(
                    f,
                    "Mutable paths overlap: {} and {} when calling {}",
                    fmt_span(a_span),
                    fmt_span(b_span),
                    fmt_span(fn_span),
                )
            }
            UndefinedVarInStringFormatting {
                var_span,
                string_span,
            } => {
                write!(
                    f,
                    "Undefined variable {} used in string formatting {}",
                    fmt_span(var_span),
                    fmt_span(string_span),
                )
            }
            InvalidEffectDependency {
                source,
                source_span,
                target,
                target_span,
            } => {
                write!(
                    f,
                    "Invalid effect dependency: `{}` due to {} is incompatible with `{}` due to {}",
                    source,
                    fmt_span(source_span),
                    target,
                    fmt_span(target_span),
                )
            }
            UnknownProperty {
                scope,
                variable,
                cause,
                ..
            } => {
                write!(
                    f,
                    "Unknown {} property: `{}.{}`",
                    cause.as_prefix(),
                    scope,
                    variable
                )
            }
            Unsupported { span, reason } => {
                write!(f, "Unsupported: {} in {}", reason, fmt_span(span))
            }
            /*UnresolvedImport {
                function_path,
                span,
            } => {
                write!(f, "Unresolved import: `{}` in `{}`", function_path, fmt_span(span))
            }
            ImportSignatureMismatch {
                function_path,
                expected_signature,
                got_signature,
                span,
            } => {
                write!(
                    f,
                    "Import signature mismatch for `{}`: expected `{}`, got `{}` in `{}`",
                    function_path,
                    expected_signature,
                    got_signature,
                    fmt_span(span)
                )
            }*/
            CircularImportDependency {
                origin,
                import_chain,
                span,
            } => write!(
                f,
                "Circular import dependency from {}: {} -> {} in `{}`",
                origin,
                import_chain.iter().join(" -> "),
                import_chain[0],
                fmt_span(span)
            ),
            Internal { span, error } => write!(f, "ICE: {} in {}", error, fmt_span(span)),
        }
    }
}

#[macro_export]
macro_rules! compilation_error {
    ($($ctor:tt)*) => {
        CompilationError::new(
            $crate::compiler::error::CompilationErrorImpl::$($ctor)*
        )
    };
}

impl CompilationError {
    pub fn resolve_types(
        error: InternalCompilationError,
        env: &ModuleEnv<'_>,
        source_table: &SourceTable,
    ) -> Self {
        use CompilationErrorImpl::*;
        match error.into_inner() {
            ParsingFailed(errors) => compilation_error!(ParsingFailed(errors)),
            NameDefinedMultipleTimes {
                name,
                first_occurrence,
                second_occurrence,
            } => compilation_error!(NameDefinedMultipleTimes {
                name,
                first_occurrence,
                second_occurrence,
            }),
            NameImportedMultipleTimes { name, occurrences } => {
                compilation_error!(NameImportedMultipleTimes { name, occurrences })
            }
            ImportConflictsWithLocalDefinition {
                name,
                definition_span,
                import_site,
            } => compilation_error!(ImportConflictsWithLocalDefinition {
                name,
                definition_span,
                import_site,
            }),
            ImportNotFound(site) => {
                compilation_error!(ImportNotFound(site))
            }
            TypeNotFound(span) => compilation_error!(TypeNotFound(span)),
            EffectNotFound { name, span } => compilation_error!(EffectNotFound { name, span }),
            TraitNotFound(span) => compilation_error!(TraitNotFound(span)),
            InvalidGenericParams { owner, kind, span } => {
                compilation_error!(InvalidGenericParams { owner, kind, span })
            }
            InvalidTraitConstraint {
                trait_name,
                kind,
                span,
            } => compilation_error!(InvalidTraitConstraint {
                trait_name,
                kind,
                span,
            }),
            InvalidTraitDefinition {
                trait_name,
                kind,
                span,
            } => compilation_error!(InvalidTraitDefinition {
                trait_name,
                kind,
                span,
            }),
            UnsupportedTraitDefinition {
                trait_name,
                kind,
                span,
            } => compilation_error!(UnsupportedTraitDefinition {
                trait_name,
                kind,
                span,
            }),
            InvalidEnumDefaultAttribute {
                type_name,
                kind,
                span,
            } => compilation_error!(InvalidEnumDefaultAttribute {
                type_name,
                kind,
                span,
            }),
            InvalidAttribute {
                attribute_name,
                target,
                kind,
                span,
            } => compilation_error!(InvalidAttribute {
                attribute_name,
                target,
                kind,
                span,
            }),
            WrongNumberOfArguments {
                expected,
                expected_span,
                got,
                got_span,
            } => compilation_error!(WrongNumberOfArguments {
                expected,
                expected_span,
                got,
                got_span,
            }),
            MutabilityMustBe {
                source_span,
                reason_span,
                what,
                ctx,
            } => {
                let (source_span, reason_span) =
                    resolve_must_be_mutable_ctx(source_span, reason_span, ctx, source_table);
                compilation_error!(MutabilityMustBe {
                    source_span,
                    reason_span,
                    what,
                    ctx
                })
            }
            TypeMismatch {
                current_ty,
                current_span,
                expected_ty,
                expected_span,
                sub_or_same,
            } => compilation_error!(TypeMismatch {
                current_ty: current_ty.format_with(env).to_string(),
                current_span,
                expected_ty: expected_ty.format_with(env).to_string(),
                expected_span,
                sub_or_same,
            }),
            NamedTypeMismatch {
                current_decl,
                current_span,
                expected_decl,
                expected_span,
            } => {
                let current_decl = type_def_origin_from_internal(current_decl, current_span, env);
                let expected_decl =
                    type_def_origin_from_internal(expected_decl, expected_span, env);
                compilation_error!(NamedTypeMismatch {
                    current_decl,
                    current_span,
                    expected_decl,
                    expected_span,
                })
            }
            PrivateReprAccess {
                type_def,
                access_span,
            } => {
                let type_def = type_def_origin_from_internal(type_def, access_span, env);
                compilation_error!(PrivateReprAccess {
                    type_def,
                    access_span
                })
            }
            InfiniteType { kind, span } => {
                let kind = match kind {
                    InfiniteTypeKind::TypeVariableCycle { ty_var, ty } => {
                        InfiniteTypeKind::TypeVariableCycle {
                            ty_var: ty_var.to_string(),
                            ty: ty.format_with(env).to_string(),
                        }
                    }
                    InfiniteTypeKind::TypeVariableSumCycleWithoutTerminatingVariant {
                        ty_var,
                        ty,
                    } => InfiniteTypeKind::TypeVariableSumCycleWithoutTerminatingVariant {
                        ty_var: ty_var.to_string(),
                        ty: ty.format_with(env).to_string(),
                    },
                    InfiniteTypeKind::ProductCycleWithoutSum { name } => {
                        InfiniteTypeKind::ProductCycleWithoutSum { name }
                    }
                    InfiniteTypeKind::SumCycleWithoutTerminatingVariant { name } => {
                        InfiniteTypeKind::SumCycleWithoutTerminatingVariant { name }
                    }
                };
                compilation_error!(InfiniteType { kind, span })
            }
            InvalidRecursiveType { kind, span } => {
                compilation_error!(InvalidRecursiveType { kind, span })
            }
            UnboundTypeVar { ty_var, ty, span } => compilation_error!(UnboundTypeVar {
                ty_var: ty_var.to_string(),
                ty: ty.format_with(env).to_string(),
                span,
            }),
            UnresolvedConstraints { constraints, span } => {
                compilation_error!(UnresolvedConstraints {
                    constraints: constraints
                        .iter()
                        .map(|c| c.format_with(env).to_string())
                        .collect(),
                    span,
                })
            }
            InvalidTupleIndex {
                index,
                index_span,
                tuple_length,
                tuple_span,
            } => compilation_error!(InvalidTupleIndex {
                index,
                index_span,
                tuple_length,
                tuple_span,
            }),
            InvalidTupleProjection {
                expr_ty,
                expr_span,
                index_span,
            } => compilation_error!(InvalidTupleProjection {
                expr_ty: expr_ty.format_with(env).to_string(),
                expr_span,
                index_span,
            }),
            DuplicatedField {
                first_occurrence,
                second_occurrence,
                constructor_span,
                ctx,
            } => compilation_error!(DuplicatedField {
                first_occurrence,
                second_occurrence,
                constructor_span,
                ctx,
            }),
            InvalidRecordField {
                field_span,
                record_ty,
                record_span,
            } => compilation_error!(InvalidRecordField {
                field_span,
                record_ty: record_ty.format_with(env).to_string(),
                record_span,
            }),
            InvalidRecordFieldAccess {
                field_span,
                record_ty,
                record_span,
            } => compilation_error!(InvalidRecordFieldAccess {
                field_span,
                record_ty: record_ty.format_with(env).to_string(),
                record_span,
            }),
            InvalidVariantName { name, ty, .. } => compilation_error!(InvalidVariantName {
                name,
                ty: ty.format_with(env).to_string(),
                valid: ty
                    .data()
                    .as_variant()
                    .unwrap()
                    .iter()
                    .map(|(name, _)| name.to_string())
                    .collect(),
            }),
            InvalidVariantType { name, ty } => compilation_error!(InvalidVariantType {
                name,
                ty: ty.format_with(env).to_string(),
            }),
            InvalidVariantConstructor { span } => {
                compilation_error!(InvalidVariantConstructor { span })
            }
            ReturnOutsideFunction { span } => {
                compilation_error!(ReturnOutsideFunction { span })
            }
            IsNotCorrectProductType {
                which,
                type_def,
                what,
                instantiation_span,
            } => {
                let type_def = type_def_origin_from_internal(type_def, instantiation_span, env);
                compilation_error!(IsNotCorrectProductType {
                    which,
                    type_def,
                    what,
                    instantiation_span,
                })
            }
            InvalidStructField {
                type_def,
                field_name,
                field_span,
                instantiation_span,
            } => {
                let type_def = type_def_origin_from_internal(type_def, instantiation_span, env);
                compilation_error!(InvalidStructField {
                    type_def,
                    field_name,
                    field_span,
                    instantiation_span,
                })
            }
            MissingStructField {
                type_def,
                field_name,
                instantiation_span,
            } => {
                let type_def = type_def_origin_from_internal(type_def, instantiation_span, env);
                compilation_error!(MissingStructField {
                    type_def,
                    field_name,
                    instantiation_span,
                })
            }
            InconsistentADT {
                a_type,
                a_span,
                b_type,
                b_span,
            } => compilation_error!(InconsistentADT {
                a_type,
                a_span,
                b_type,
                b_span,
            }),
            InconsistentPattern {
                a_type,
                a_span,
                b_type,
                b_span,
            } => compilation_error!(InconsistentPattern {
                a_type,
                a_span,
                b_type,
                b_span,
            }),
            DuplicatedVariant {
                first_occurrence,
                second_occurrence,
                ctx_span,
                ctx,
            } => compilation_error!(DuplicatedVariant {
                first_occurrence,
                second_occurrence,
                ctx_span,
                ctx
            }),
            VariantNameConflictsWithType { name, span } => {
                compilation_error!(VariantNameConflictsWithType { name, span })
            }
            RecordWildcardPatternNotAtEnd {
                pattern_span,
                wildcard_span,
            } => {
                compilation_error!(RecordWildcardPatternNotAtEnd {
                    pattern_span,
                    wildcard_span
                })
            }
            TraitImplNotFound {
                trait_ref,
                input_tys,
                fn_span,
            } => compilation_error!(TraitImplNotFound {
                trait_ref: env.trait_name(trait_ref).to_string(),
                input_tys: input_tys
                    .iter()
                    .zip(env.trait_def(trait_ref).input_type_names.iter())
                    .map(|(ty, name)| format!("{name} = {}", ty.format_with(env)))
                    .collect(),
                fn_span,
            }),
            TraitSolverRecursionLimitExceeded {
                trait_ref,
                input_tys,
                fn_span,
            } => compilation_error!(TraitSolverRecursionLimitExceeded {
                trait_ref: env.trait_name(trait_ref).to_string(),
                input_tys: input_tys
                    .iter()
                    .zip(env.trait_def(trait_ref).input_type_names.iter())
                    .map(|(ty, name)| format!("{name} = {}", ty.format_with(env)))
                    .collect(),
                fn_span,
            }),
            TraitSolverCycleDetected {
                trait_ref,
                input_tys,
                fn_span,
            } => compilation_error!(TraitSolverCycleDetected {
                trait_ref: env.trait_name(trait_ref).to_string(),
                input_tys: input_tys
                    .iter()
                    .zip(env.trait_def(trait_ref).input_type_names.iter())
                    .map(|(ty, name)| format!("{name} = {}", ty.format_with(env)))
                    .collect(),
                fn_span,
            }),
            MethodsNotPartOfTrait { trait_ref, spans } => {
                compilation_error!(MethodsNotPartOfTrait {
                    trait_ref: env.trait_name(trait_ref).to_string(),
                    spans
                })
            }
            TraitMethodImplsMissing {
                trait_ref,
                missings,
                impl_span,
            } => compilation_error!(TraitMethodImplsMissing {
                trait_ref: env.trait_name(trait_ref).to_string(),
                missings,
                impl_span,
            }),
            InvalidTraitAssociatedConstImpl {
                trait_ref,
                kind,
                span,
            } => compilation_error!(InvalidTraitAssociatedConstImpl {
                trait_ref: env.trait_name(trait_ref).to_string(),
                kind,
                span,
            }),
            TraitImplOrphanRuleViolation {
                trait_ref,
                input_tys,
                impl_span,
            } => compilation_error!(TraitImplOrphanRuleViolation {
                trait_ref: env.trait_name(trait_ref).to_string(),
                input_tys: input_tys
                    .iter()
                    .zip(env.trait_def(trait_ref).input_type_names.iter())
                    .map(|(ty, name)| format!("{name} = {}", ty.format_with(env)))
                    .collect(),
                impl_span,
            }),
            TraitImplForAnonymousStructuralType {
                input_ty,
                impl_span,
            } => compilation_error!(TraitImplForAnonymousStructuralType {
                input_ty: input_ty.format_with(env).to_string(),
                impl_span,
            }),
            TraitImplNativeOnly {
                trait_ref,
                impl_span,
            } => compilation_error!(TraitImplNativeOnly {
                trait_ref: env.trait_name(trait_ref).to_string(),
                impl_span,
            }),
            OverlappingTraitImpls {
                trait_ref,
                input_tys,
                impl_span,
                existing_impl,
                existing_span,
            } => compilation_error!(OverlappingTraitImpls {
                trait_ref: env.trait_name(trait_ref).to_string(),
                input_tys: input_tys
                    .iter()
                    .zip(env.trait_def(trait_ref).input_type_names.iter())
                    .map(|(ty, name)| format!("{name} = {}", ty.format_with(env)))
                    .collect(),
                impl_span,
                existing_impl: external_trait_impl_header_from_internal(
                    existing_impl,
                    trait_ref,
                    env
                ),
                existing_span,
            }),
            TraitMethodArgCountMismatch {
                trait_ref,
                method_name,
                method_index,
                expected,
                got,
                args_span,
            } => compilation_error!(TraitMethodArgCountMismatch {
                trait_ref: env.trait_name(trait_ref).to_string(),
                method_name,
                method_index,
                expected,
                got,
                args_span,
            }),
            TraitMethodEffectMismatch {
                trait_ref,
                method_name,
                expected,
                got,
                span,
            } => compilation_error!(TraitMethodEffectMismatch {
                trait_ref: env.trait_name(trait_ref).to_string(),
                method_name,
                expected,
                got,
                span,
            }),
            CompilerOnlyTraitMethodUse {
                trait_ref,
                method_name,
                span,
            } => compilation_error!(CompilerOnlyTraitMethodUse {
                trait_ref: env.trait_name(trait_ref).to_string(),
                method_name,
                span,
            }),
            UnsafeFeatureUseNotAllowed { feature, span } => {
                compilation_error!(UnsafeFeatureUseNotAllowed { feature, span })
            }
            InvalidLoopControl {
                control,
                kind,
                span,
            } => compilation_error!(InvalidLoopControl {
                control,
                kind,
                span,
            }),
            IdentifierBoundMoreThanOnceInAPattern {
                first_occurrence,
                second_occurrence,
                pattern_span,
            } => compilation_error!(IdentifierBoundMoreThanOnceInAPattern {
                first_occurrence,
                second_occurrence,
                pattern_span,
            }),
            DuplicatedLiteralPattern {
                first_occurrence,
                second_occurrence,
                match_span,
            } => compilation_error!(DuplicatedLiteralPattern {
                first_occurrence,
                second_occurrence,
                match_span,
            }),
            EmptyMatchBody { span: cond_span } => {
                compilation_error!(EmptyMatchBody { span: cond_span })
            }
            NonExhaustivePattern { span, ty } => compilation_error!(NonExhaustivePattern {
                span,
                ty: ty.format_with(env).to_string(),
            }),
            TypeValuesCannotBeEnumerated { span, ty } => {
                compilation_error!(TypeValuesCannotBeEnumerated {
                    span,
                    ty: ty.format_with(env).to_string(),
                })
            }
            MutablePathsOverlap {
                a_span,
                b_span,
                fn_span,
            } => compilation_error!(MutablePathsOverlap {
                a_span,
                b_span,
                fn_span,
            }),
            UndefinedVarInStringFormatting {
                var_span,
                string_span,
            } => compilation_error!(UndefinedVarInStringFormatting {
                var_span,
                string_span,
            }),
            InvalidEffectDependency {
                source,
                source_span,
                target,
                target_span,
            } => compilation_error!(InvalidEffectDependency {
                source,
                source_span,
                target,
                target_span,
            }),
            UnknownProperty {
                scope,
                variable,
                cause,
                span,
            } => compilation_error!(UnknownProperty {
                scope,
                variable,
                cause,
                span,
            }),
            Unsupported { span, reason } => compilation_error!(Unsupported { span, reason }),
            /*UnresolvedImport {
                function_path,
                span,
            } => compilation_error!(UnresolvedImport {
                function_path,
                span,
            }),
            ImportSignatureMismatch {
                function_path,
                expected_signature,
                got_signature,
                span,
            } => compilation_error!(ImportSignatureMismatch {
                function_path,
                expected_signature,
                got_signature,
                span,
            }),*/
            CircularImportDependency {
                origin,
                import_chain,
                span,
            } => {
                compilation_error!(CircularImportDependency {
                    origin,
                    import_chain,
                    span
                })
            }
            Internal { span, error } => compilation_error!(Internal { span, error }),
        }
    }
}
