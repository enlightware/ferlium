// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use std::{
    fmt::{self, Display},
    ops::Deref,
};

use crate::{
    CompilationError, Location, SourceId,
    compiler::error::{
        CompilationErrorImpl, ImportKind, MutabilityMustBeWhat, WhatIsNotAProductType,
        WhichProductTypeIsNot,
    },
    parser::location::SourceTable,
};
use itertools::Itertools;
#[cfg(target_arch = "wasm32")]
use wasm_bindgen::prelude::*;

/// An error-data structure to be used in IDEs
#[cfg_attr(target_arch = "wasm32", wasm_bindgen(getter_with_clone))]
#[derive(Debug, Clone)]
pub struct ErrorData {
    pub(super) source_id: SourceId,
    pub from: u32,
    pub to: u32,
    pub file: String,
    pub text: String,
}

#[cfg_attr(target_arch = "wasm32", wasm_bindgen)]
impl ErrorData {
    pub(super) fn from_location(loc: Location, source_table: &SourceTable, text: String) -> Self {
        Self {
            source_id: loc.source_id(),
            from: loc.start(),
            to: loc.end(),
            file: source_table
                .get_source_name(loc.source_id())
                .unwrap_or(&format!("#{}", loc.source_id()))
                .to_string(),
            text,
        }
    }

    pub(crate) fn map(self, mut f: impl FnMut(u32) -> u32) -> Self {
        Self {
            source_id: self.source_id,
            from: f(self.from),
            to: f(self.to),
            file: self.file,
            text: self.text,
        }
    }
}

impl Display for ErrorData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.text)
    }
}

pub(super) fn compilation_error_to_data(
    error: &CompilationError,
    source_table: &SourceTable,
) -> Vec<ErrorData> {
    let fmt_span = |span: &Location| {
        let start = span.start_usize();
        let end = span.end_usize();
        let source_id = span.source_id();
        match source_table.get_source_text(source_id) {
            Some(source) => {
                let position = source_table.get_line_column(source_id, start);
                let snippet = &source[start..end];
                format!(
                    "{} (in {}:{}:{})",
                    snippet, source_id, position.0, position.1
                )
            }
            None => {
                format!("#{}:{}..{}", source_id, start, end)
            }
        }
    };
    use CompilationErrorImpl::*;
    let error_data_from_location =
        |loc: &Location, msg: String| ErrorData::from_location(*loc, source_table, msg);
    match error.deref() {
        ParsingFailed(errors) => errors
            .iter()
            .map(|(msg, span)| error_data_from_location(span, msg.clone()))
            .collect(),
        NameDefinedMultipleTimes {
            name,
            first_occurrence,
            second_occurrence,
        } => vec![
            error_data_from_location(
                first_occurrence,
                format!("Name `{name}` defined multiple times"),
            ),
            error_data_from_location(
                second_occurrence,
                format!("Name `{name}` defined multiple times"),
            ),
        ],
        NameImportedMultipleTimes { name, occurrences } => occurrences
            .iter()
            .map(|import_site| {
                error_data_from_location(
                    &import_site.span,
                    format!(
                        "Name `{name}` imported multiple times, here from module `{}`",
                        import_site.module
                    ),
                )
            })
            .collect(),
        ImportConflictsWithLocalDefinition {
            name,
            definition_span,
            import_site: import_span,
        } => vec![
            error_data_from_location(
                definition_span,
                format!(
                    "Local definition of `{name}` conflicts with import from module `{}`",
                    import_span.module
                ),
            ),
            error_data_from_location(
                &import_span.span,
                format!(
                    "Import of `{name}` from module `{}` conflicts with local definition",
                    import_span.module
                ),
            ),
        ],
        ImportNotFound(site) => {
            vec![error_data_from_location(
                &site.span,
                match &site.kind {
                    ImportKind::Symbol(symbol) => format!(
                        "Import of `{}` not found in module `{}`",
                        symbol, site.module
                    ),
                    ImportKind::Module => format!("Module {} does not exist", site.module),
                },
            )]
        }
        TypeNotFound(span) => vec![error_data_from_location(
            span,
            format!("Cannot find type `{}` in this scope", fmt_span(span)),
        )],
        TraitNotFound(span) => vec![error_data_from_location(
            span,
            format!("Cannot find trait `{}` in this scope", fmt_span(span)),
        )],
        InvalidGenericParams { owner, kind, span } => {
            vec![error_data_from_location(span, kind.message(*owner))]
        }
        InvalidTraitConstraint {
            trait_name,
            kind,
            span,
        } => vec![error_data_from_location(span, kind.message(trait_name))],
        InvalidTraitDefinition {
            trait_name,
            kind,
            span,
        } => vec![error_data_from_location(span, kind.message(*trait_name))],
        UnsupportedTraitDefinition {
            trait_name,
            kind,
            span,
        } => vec![error_data_from_location(span, kind.message(*trait_name))],
        InvalidEnumDefaultAttribute {
            type_name,
            kind,
            span,
        } => vec![error_data_from_location(span, kind.message(*type_name))],
        WrongNumberOfArguments {
            expected,
            expected_span,
            got,
            got_span,
        } => vec![
            error_data_from_location(
                expected_span,
                format!("Expected {expected} arguments here, but {got} were provided"),
            ),
            error_data_from_location(
                got_span,
                format!("Expected {expected} arguments, but {got} are provided here"),
            ),
        ],
        MutabilityMustBe {
            source_span,
            reason_span,
            what,
            ..
        } => vec![error_data_from_location(source_span, {
            use MutabilityMustBeWhat::*;
            match what {
                Mutable => format!(
                    "Expression must be mutable due to `{}`",
                    fmt_span(reason_span)
                ),
                Constant => format!(
                    "Expression must be constant due to `{}`",
                    fmt_span(reason_span)
                ),
                Equal => format!(
                    "Expression must be of the same mutability as `{}`",
                    fmt_span(reason_span)
                ),
            }
        })],
        TypeMismatch {
            current_ty,
            current_span,
            expected_ty,
            ..
        } => vec![error_data_from_location(
            current_span,
            format!("Type `{current_ty}` is incompatible with type `{expected_ty}`"),
        )],
        NamedTypeMismatch {
            current_decl,
            current_span,
            expected_decl,
            ..
        } => vec![error_data_from_location(
            current_span,
            format!(
                "Named type `{}` from `{}` is different from named type `{}` from `{}`",
                current_decl.0,
                fmt_span(&current_decl.1),
                expected_decl.0,
                fmt_span(&expected_decl.1),
            ),
        )],
        InfiniteType(ty_var, ty, span) => vec![error_data_from_location(
            span,
            format!("Infinite type: `{ty_var}` = `{ty}`"),
        )],
        UnboundTypeVar { ty_var, ty, span } => vec![error_data_from_location(
            span,
            format!("Unbound type variable `{ty_var}` in `{ty}`"),
        )],
        UnresolvedConstraints { constraints, span } => vec![error_data_from_location(
            span,
            format!("Unresolved constraints: `{}`", constraints.join(" ∧ ")),
        )],
        InvalidTupleIndex {
            index,
            index_span,
            tuple_length,
            ..
        } => vec![error_data_from_location(
            index_span,
            format!("Invalid index {index} of a tuple of length {tuple_length}"),
        )],
        InvalidTupleProjection {
            expr_ty,
            expr_span,
            index_span,
        } => {
            let index_name = fmt_span(index_span);
            vec![error_data_from_location(
                expr_span,
                format!(
                    "Expected tuple because of `.{index_name}`, but `{expr_ty}` was provided instead"
                ),
            )]
        }
        DuplicatedField {
            first_occurrence,
            second_occurrence,
            ..
        } => {
            let name = fmt_span(first_occurrence);
            let text = format!("Duplicated field `{name}`");
            vec![
                error_data_from_location(first_occurrence, text.clone()),
                error_data_from_location(second_occurrence, text),
            ]
        }
        InvalidRecordField {
            field_span,
            record_ty,
            ..
        } => {
            let field_name = fmt_span(field_span);
            vec![error_data_from_location(
                field_span,
                format!("Field `{field_name}` not found in record `{record_ty}`"),
            )]
        }
        InvalidRecordFieldAccess {
            field_span,
            record_ty,
            ..
        } => {
            let field_name = fmt_span(field_span);
            vec![error_data_from_location(
                field_span,
                format!(
                    "Expected record because of `.{field_name}`, but `{record_ty}` was provided instead"
                ),
            )]
        }
        InvalidVariantName { name, ty, valid } => {
            let name_text = fmt_span(name);
            vec![error_data_from_location(
                name,
                format!(
                    "Variant name `{name_text}` does not exist for variant type `{ty}`, valid names are `{}`",
                    valid.join(", ")
                ),
            )]
        }
        InvalidVariantType { name, ty } => {
            let name_text = fmt_span(name);
            vec![error_data_from_location(
                name,
                format!(
                    "Type `{ty}` is not a variant, but variant constructor `{name_text}` requires it"
                ),
            )]
        }
        InvalidVariantConstructor { span } => {
            vec![error_data_from_location(
                span,
                "Variant constructor cannot be a path".to_string(),
            )]
        }
        ReturnOutsideFunction { span } => {
            vec![error_data_from_location(
                span,
                "Return statement can only be used inside a function, but found within an expression".to_string(),
            )]
        }
        IsNotCorrectProductType {
            which,
            type_def,
            what,
            instantiation_span,
        } => {
            use WhichProductTypeIsNot::*;
            let which = match which {
                Unit => "arguments, but none are provided here",
                Record => "a record, but none is provided here",
                Tuple => "a tuple, but none is provided here",
            };
            let what = match what {
                WhatIsNotAProductType::EnumVariant(tag) => {
                    format!("Variant `{tag}` of `{}`", type_def.0)
                }
                WhatIsNotAProductType::Struct => format!("`{}`", type_def.0),
            };
            vec![error_data_from_location(
                instantiation_span,
                format!("{what} requires {which}"),
            )]
        }
        InvalidStructField {
            type_def,
            field_span,
            ..
        } => {
            let field_name = fmt_span(field_span);
            vec![error_data_from_location(
                field_span,
                format!("Field `{field_name}` does not exists in `{}`", type_def.0),
            )]
        }
        MissingStructField {
            type_def,
            field_name,
            instantiation_span,
        } => {
            vec![error_data_from_location(
                instantiation_span,
                format!("Field `{field_name}` from `{}` is missing here", type_def.0),
            )]
        }
        InconsistentADT {
            a_type,
            a_span,
            b_type,
            b_span,
        } => {
            let a_name = a_type.adt_kind();
            let b_name = b_type.adt_kind();
            vec![
                error_data_from_location(
                    a_span,
                    format!("Data type {a_name} here is different than data type {b_name}"),
                ),
                error_data_from_location(
                    b_span,
                    format!("Data type {b_name} here is different than data type {a_name}"),
                ),
            ]
        }
        InconsistentPattern {
            a_type,
            a_span,
            b_type,
            b_span,
        } => {
            let a_name = a_type.name();
            let b_name = b_type.name();
            vec![
                error_data_from_location(
                    a_span,
                    format!("Pattern expects a {a_name}, but {b_name} was provided instead"),
                ),
                error_data_from_location(
                    b_span,
                    format!("Pattern expects a {b_name}, but {a_name} was provided instead"),
                ),
            ]
        }
        DuplicatedVariant {
            first_occurrence,
            second_occurrence,
            ..
        } => {
            let name = fmt_span(first_occurrence);
            let text = format!("Duplicated variant `{name}`");
            vec![
                error_data_from_location(first_occurrence, text.clone()),
                error_data_from_location(second_occurrence, text),
            ]
        }
        RecordWildcardPatternNotAtEnd { pattern_span, .. } => {
            vec![error_data_from_location(
                pattern_span,
                "Record wildcard pattern .. must be at the end of the pattern".to_string(),
            )]
        }
        TraitImplNotFound {
            trait_ref,
            input_tys,
            fn_span,
        } => {
            vec![error_data_from_location(
                fn_span,
                format!(
                    "Implementation of trait `{trait_ref}` over types `{}` not found",
                    input_tys.join(", ")
                ),
            )]
        }
        TraitSolverRecursionLimitExceeded {
            trait_ref,
            input_tys,
            fn_span,
        } => {
            vec![error_data_from_location(
                fn_span,
                format!(
                    "Recursion limit exceeded while solving trait implementation for `{trait_ref}` over types `{}`",
                    input_tys.join(", ")
                ),
            )]
        }
        TraitSolverCycleDetected {
            trait_ref,
            input_tys,
            fn_span,
        } => {
            vec![error_data_from_location(
                fn_span,
                format!(
                    "Cycle detected while solving trait implementation for `{trait_ref}` over types `{}`",
                    input_tys.join(", ")
                ),
            )]
        }
        MethodsNotPartOfTrait { trait_ref, spans } => spans
            .iter()
            .map(|span| {
                error_data_from_location(
                    span,
                    format!(
                        "Method `{}` is not part of trait `{}`",
                        fmt_span(span),
                        trait_ref
                    ),
                )
            })
            .collect(),
        TraitMethodImplsMissing {
            trait_ref,
            missings,
            impl_span,
        } => {
            vec![error_data_from_location(
                impl_span,
                format!(
                    "Implementation of trait `{}` is missing methods: `{}`",
                    trait_ref,
                    missings.iter().map(|m| m.as_ref()).join(", "),
                ),
            )]
        }
        TraitImplOrphanRuleViolation {
            trait_ref,
            input_tys,
            impl_span,
        } => {
            vec![error_data_from_location(
                impl_span,
                format!(
                    "Implementation of foreign trait `{trait_ref}` over types `{}` violates the orphan rule",
                    input_tys.join(", ")
                ),
            )]
        }
        TraitImplNativeOnly {
            trait_ref,
            impl_span,
        } => {
            vec![error_data_from_location(
                impl_span,
                format!("Trait `{trait_ref}` can only be implemented by trusted native code"),
            )]
        }
        OverlappingTraitImpls {
            trait_ref,
            input_tys,
            impl_span,
            existing_impl,
            existing_span,
        } => {
            let mut diagnostics = vec![error_data_from_location(
                impl_span,
                format!(
                    "Implementation of trait `{trait_ref}` over types `{}` overlaps with existing impl `{existing_impl}`",
                    input_tys.join(", "),
                    existing_impl = existing_impl.display(trait_ref)
                ),
            )];
            if let Some(existing_span) = existing_span {
                diagnostics.push(error_data_from_location(
                    existing_span,
                    format!(
                        "Conflicting implementation: {}",
                        existing_impl.display(trait_ref)
                    ),
                ));
            }
            diagnostics
        }
        TraitMethodArgCountMismatch {
            trait_ref,
            method_name,
            expected,
            got,
            args_span,
            ..
        } => {
            vec![error_data_from_location(
                args_span,
                format!(
                    "Method `{}` of trait `{}` expects {} arguments, got {}",
                    method_name, trait_ref, expected, got
                ),
            )]
        }
        TraitMethodEffectMismatch {
            trait_ref,
            method_name,
            expected,
            got,
            span,
        } => {
            vec![error_data_from_location(
                span,
                format!(
                    "Method `{}` of trait `{}` has effects `{}`, but implementation has effects `{}`",
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
                ),
            )]
        }
        IdentifierBoundMoreThanOnceInAPattern {
            first_occurrence,
            second_occurrence,
            ..
        } => {
            let name_text = fmt_span(first_occurrence);
            let text = format!("Identifier `{name_text}` bound more than once in a pattern");
            vec![
                error_data_from_location(first_occurrence, text.clone()),
                error_data_from_location(second_occurrence, text),
            ]
        }
        DuplicatedLiteralPattern {
            first_occurrence,
            second_occurrence,
            ..
        } => {
            let name_text = fmt_span(first_occurrence);
            let text = format!("Duplicated literal pattern `{name_text}`");
            vec![
                error_data_from_location(first_occurrence, text.clone()),
                error_data_from_location(second_occurrence, text),
            ]
        }
        EmptyMatchBody { span } => vec![error_data_from_location(
            span,
            "Match body cannot be empty".to_string(),
        )],
        NonExhaustivePattern { span, ty } => {
            vec![error_data_from_location(
                span,
                format!(
                    "Non-exhaustive patterns for type `{ty}`, all possible values must be covered"
                ),
            )]
        }
        TypeValuesCannotBeEnumerated { span, ty } => {
            vec![error_data_from_location(
                span,
                format!(
                    "Values of type `{ty}` cannot be enumerated, but all possible values must be known for exhaustive match coverage analysis"
                ),
            )]
        }
        MutablePathsOverlap {
            a_span,
            b_span,
            fn_span,
        } => {
            let a_name = fmt_span(a_span);
            let b_name = fmt_span(b_span);
            let fn_name = fmt_span(fn_span);
            vec![
                error_data_from_location(
                    a_span,
                    format!(
                        "Mutable path `{a_name}` (here) overlaps with `{b_name}` when calling function `{fn_name}`"
                    ),
                ),
                error_data_from_location(
                    b_span,
                    format!(
                        "Mutable path `{a_name}` overlaps with `{b_name}` (here) when calling function `{fn_name}`"
                    ),
                ),
                error_data_from_location(
                    fn_span,
                    format!(
                        "When calling function `{fn_name}`: mutable path `{a_name}` overlaps with `{b_name}`"
                    ),
                ),
            ]
        }
        UndefinedVarInStringFormatting {
            var_span,
            string_span,
        } => {
            let var_text = fmt_span(var_span);
            let string_text = fmt_span(string_span);
            vec![error_data_from_location(
                var_span,
                format!(
                    "Undefined variable `{var_text}` used in string formatting: `{string_text}`"
                ),
            )]
        }
        InvalidEffectDependency {
            source,
            source_span,
            target,
            ..
        } => {
            vec![error_data_from_location(
                source_span,
                format!("Effect `{source}` cannot depend on `{target}`"),
            )]
        }
        UnknownProperty {
            scope,
            variable,
            span,
            ..
        } => {
            vec![error_data_from_location(
                span,
                format!("Unknown property `{scope}.{variable}`"),
            )]
        }
        Unsupported { span, reason } => vec![error_data_from_location(span, reason.to_string())],
        CircularImportDependency {
            origin,
            import_chain,
            span,
        } => vec![error_data_from_location(
            span,
            format!(
                "Circular import dependency detected `{origin}`: {} -> `{}`",
                import_chain.iter().map(|s| format!("`{s}`")).join(" -> "),
                import_chain[0],
            ),
        )],
        Internal { span, error } => vec![error_data_from_location(
            span,
            format!("Internal compiler error: {error}"),
        )],
    }
}
