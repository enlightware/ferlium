// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use std::ops::Deref;

use crate::{
    Location, SourceId, SourceTable,
    compiler::{
        error::{CompilationError, CompilationErrorImpl},
        session::{CompilationRevision, SourceVersion},
    },
    format::FormatWith,
    module::ModuleId,
};

/// A source diagnostic produced by the latest compilation attempt for a module.
#[derive(Debug, Clone)]
pub struct ModuleDiagnostic {
    /// Module whose compilation produced this diagnostic.
    pub module_id: ModuleId,
    /// Source version that was compiled when this diagnostic was produced.
    pub source_version: SourceVersion,
    /// Source table entry containing the text referenced by [`location`](Self::location).
    pub source_id: SourceId,
    /// Primary source span for the diagnostic.
    ///
    /// Some compiler errors have multiple relevant spans. In that case they are
    /// represented as multiple diagnostics with the same message and different
    /// primary locations.
    pub location: Location,
    /// Compilation attempt that produced this diagnostic.
    pub compilation_revision: CompilationRevision,
    /// Human-readable diagnostic message.
    pub message: String,
}

/// Convert a structured compiler error into module diagnostics.
///
/// This keeps the source locations from the error instead of only formatting it
/// as one string. Errors with multiple important spans become multiple
/// diagnostics that share the same message.
pub(crate) fn diagnostics_from_error(
    module_id: ModuleId,
    source_version: SourceVersion,
    compilation_revision: CompilationRevision,
    source_id: SourceId,
    error: &CompilationError,
    source_table: &SourceTable,
) -> Vec<ModuleDiagnostic> {
    let message = format!("{}", error.format_with(source_table));
    let diagnostic = |location: Location| ModuleDiagnostic {
        module_id,
        source_version,
        compilation_revision,
        source_id,
        location,
        message: message.clone(),
    };

    use CompilationErrorImpl::*;
    let locations: Vec<Location> = match error.deref() {
        ParsingFailed(errors) => {
            return errors
                .iter()
                .map(|(message, location)| ModuleDiagnostic {
                    module_id,
                    source_version,
                    compilation_revision,
                    source_id,
                    location: *location,
                    message: message.clone(),
                })
                .collect();
        }
        NameDefinedMultipleTimes {
            first_occurrence,
            second_occurrence,
            ..
        } => vec![*first_occurrence, *second_occurrence],
        NameImportedMultipleTimes { occurrences, .. } => {
            occurrences.iter().map(|site| site.span).collect()
        }
        ImportConflictsWithLocalDefinition {
            definition_span,
            import_site,
            ..
        } => vec![*definition_span, import_site.span],
        ImportNotFound(site) => vec![site.span],
        TypeNotFound(span)
        | TraitNotFound(span)
        | InvalidGenericParams { span, .. }
        | InvalidTraitConstraint { span, .. }
        | InvalidTraitDefinition { span, .. }
        | UnsupportedTraitDefinition { span, .. }
        | InvalidEnumDefaultAttribute { span, .. }
        | InfiniteType(_, _, span)
        | UnboundTypeVar { span, .. }
        | UnresolvedConstraints { span, .. }
        | InvalidVariantConstructor { span }
        | EmptyMatchBody { span }
        | NonExhaustivePattern { span, .. }
        | TypeValuesCannotBeEnumerated { span, .. }
        | Unsupported { span, .. }
        | ReturnOutsideFunction { span }
        | CircularImportDependency { span, .. }
        | Internal { span, .. } => vec![*span],
        WrongNumberOfArguments {
            expected_span,
            got_span,
            ..
        }
        | TypeMismatch {
            current_span: expected_span,
            expected_span: got_span,
            ..
        }
        | NamedTypeMismatch {
            current_span: expected_span,
            expected_span: got_span,
            ..
        }
        | MutabilityMustBe {
            source_span: expected_span,
            reason_span: got_span,
            ..
        }
        | InvalidTupleIndex {
            index_span: expected_span,
            tuple_span: got_span,
            ..
        }
        | InvalidTupleProjection {
            expr_span: expected_span,
            index_span: got_span,
            ..
        }
        | InvalidRecordField {
            field_span: expected_span,
            record_span: got_span,
            ..
        }
        | InvalidRecordFieldAccess {
            field_span: expected_span,
            record_span: got_span,
            ..
        }
        | InconsistentADT {
            a_span: expected_span,
            b_span: got_span,
            ..
        }
        | InconsistentPattern {
            a_span: expected_span,
            b_span: got_span,
            ..
        }
        | IdentifierBoundMoreThanOnceInAPattern {
            first_occurrence: expected_span,
            second_occurrence: got_span,
            ..
        }
        | DuplicatedLiteralPattern {
            first_occurrence: expected_span,
            second_occurrence: got_span,
            ..
        }
        | MutablePathsOverlap {
            a_span: expected_span,
            b_span: got_span,
            ..
        }
        | UndefinedVarInStringFormatting {
            var_span: expected_span,
            string_span: got_span,
        }
        | InvalidEffectDependency {
            source_span: expected_span,
            target_span: got_span,
            ..
        } => vec![*expected_span, *got_span],
        DuplicatedField {
            first_occurrence,
            second_occurrence,
            constructor_span,
            ..
        } => vec![*first_occurrence, *second_occurrence, *constructor_span],
        DuplicatedVariant {
            first_occurrence,
            second_occurrence,
            ctx_span,
            ..
        } => vec![*first_occurrence, *second_occurrence, *ctx_span],
        RecordWildcardPatternNotAtEnd {
            pattern_span,
            wildcard_span,
        } => vec![*pattern_span, *wildcard_span],
        InvalidVariantName { name, .. } | InvalidVariantType { name, .. } => vec![*name],
        IsNotCorrectProductType {
            instantiation_span, ..
        }
        | InvalidStructField {
            instantiation_span, ..
        }
        | MissingStructField {
            instantiation_span, ..
        }
        | TraitImplNotFound {
            fn_span: instantiation_span,
            ..
        }
        | TraitSolverRecursionLimitExceeded {
            fn_span: instantiation_span,
            ..
        }
        | TraitSolverCycleDetected {
            fn_span: instantiation_span,
            ..
        }
        | TraitImplOrphanRuleViolation {
            impl_span: instantiation_span,
            ..
        }
        | TraitImplNativeOnly {
            impl_span: instantiation_span,
            ..
        }
        | TraitMethodArgCountMismatch {
            args_span: instantiation_span,
            ..
        }
        | TraitMethodEffectMismatch {
            span: instantiation_span,
            ..
        }
        | UnknownProperty {
            span: instantiation_span,
            ..
        } => vec![*instantiation_span],
        MethodsNotPartOfTrait { spans, .. } => spans.clone(),
        TraitMethodImplsMissing { impl_span, .. } => vec![*impl_span],
        OverlappingTraitImpls {
            impl_span,
            existing_span,
            ..
        } => existing_span.map_or_else(|| vec![*impl_span], |span| vec![*impl_span, span]),
    };

    locations.into_iter().map(diagnostic).collect()
}
