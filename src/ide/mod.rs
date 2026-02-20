// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{
    collections::{HashMap, HashSet},
    fmt::{self, Display},
    ops::Deref,
    sync::LazyLock,
};

use crate::{
    CompilationError, CompilerSession, DisplayStyle, Location, ModuleAndExpr, ModuleEnv, Path,
    SourceId,
    error::{
        CompilationErrorImpl, ImportKind, MutabilityMustBeWhat, WhatIsNotAProductType,
        WhichProductTypeIsNot,
    },
    eval::{EvalCtx, ValOrMut},
    format::FormatWith,
    location::SourceTable,
    module::{ModuleFunction, ModuleRc, Modules},
    r#type::{FnArgType, Type, tuple_type},
    value::{NativeValue, Value},
};
use enum_as_inner::EnumAsInner;
use itertools::Itertools;
use regex::Regex;
#[cfg(target_arch = "wasm32")]
use wasm_bindgen::prelude::*;

mod annotations;
mod char_index_lookup;
use char_index_lookup::CharIndexLookup;

/// An error-data structure to be used in IDEs
#[cfg_attr(target_arch = "wasm32", wasm_bindgen(getter_with_clone))]
#[derive(Debug, Clone)]
pub struct ErrorData {
    source_id: SourceId,
    pub from: u32,
    pub to: u32,
    pub file: String,
    pub text: String,
}

#[cfg_attr(target_arch = "wasm32", wasm_bindgen)]
impl ErrorData {
    fn from_location(loc: Location, source_table: &SourceTable, text: String) -> Self {
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

/// A function signature data struct to be used in IDEs
#[cfg_attr(target_arch = "wasm32", wasm_bindgen(getter_with_clone))]
pub struct FunctionSignature {
    pub name: String,
    pub args: Vec<String>,
    pub doc: Option<String>,
}

fn compilation_error_to_data(
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
        Internal { span, error } => vec![error_data_from_location(
            span,
            format!("Internal compiler error: {error}"),
        )],
    }
}

/// An annotation data struct to be used in IDEs
#[cfg_attr(target_arch = "wasm32", wasm_bindgen(getter_with_clone))]
pub struct AnnotationData {
    pub pos: usize,
    pub hint: String,
}

#[cfg_attr(target_arch = "wasm32", wasm_bindgen)]
impl AnnotationData {
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen(constructor))]
    pub fn new(pos: usize, hint: String) -> Self {
        Self { pos, hint }
    }
}

/// The content of an execution error in the IDE
#[cfg_attr(target_arch = "wasm32", wasm_bindgen(getter_with_clone))]
#[derive(Debug, Clone)]
pub struct ExecutionErrorData {
    pub summary: String,
    pub complete: String,
    pub data: Option<ErrorData>,
}

#[derive(Debug, Clone, EnumAsInner)]
pub enum ExecutionResultInner {
    Success(String),
    Error(ExecutionErrorData),
}

/// The result of executing an expression in the IDE
#[cfg_attr(target_arch = "wasm32", wasm_bindgen(getter_with_clone))]
pub struct ExecutionResult(ExecutionResultInner);

#[cfg_attr(target_arch = "wasm32", wasm_bindgen)]
impl ExecutionResult {
    pub fn html_message(&self) -> String {
        use ExecutionResultInner::*;
        match &self.0 {
            Success(output) => html_escape::encode_text(&output).to_string(),
            Error(data) => {
                format!(
                    "<span class=\"error\">{}</span>",
                    html_escape::encode_text(&data.complete)
                )
            }
        }
    }

    pub fn error_content(&self) -> Option<ExecutionErrorData> {
        self.0.as_error().cloned()
    }

    pub fn error_data(&self) -> Option<ErrorData> {
        self.0.as_error().and_then(|data| data.data.clone())
    }
}

impl ExecutionResult {
    pub fn success(output: String) -> Self {
        Self(ExecutionResultInner::Success(output))
    }

    pub fn error(data: ExecutionErrorData) -> Self {
        Self(ExecutionResultInner::Error(data))
    }
}

/// The compiler to be used in the web IDE
#[cfg_attr(target_arch = "wasm32", wasm_bindgen)]
pub struct Compiler {
    session: CompilerSession,
    user_module: ModuleAndExpr,
    char_index_lookup: HashMap<SourceId, CharIndexLookup>,
}

const SRC_NAME: &str = "<ide>";
const MODULE_NAME: &str = "ide";

/// The compiler to be used in the web IDE, wasm-available part
#[cfg_attr(target_arch = "wasm32", wasm_bindgen)]
impl Compiler {
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen(constructor))]
    pub fn new() -> Self {
        let mut session = CompilerSession::new();
        let user_module = session
            .compile("", SRC_NAME, Path::single_str(MODULE_NAME))
            .unwrap();
        Self {
            session,
            user_module,
            char_index_lookup: HashMap::new(),
        }
    }

    fn compile_internal(&mut self, src: &str) -> Result<(), CompilationError> {
        self.user_module = self
            .session
            .compile(src, SRC_NAME, Path::single_str(MODULE_NAME))?;
        Ok(())
    }

    pub fn compile(&mut self, src: &str) -> Option<Vec<ErrorData>> {
        match self.compile_internal(src) {
            Ok(()) => None,
            Err(err) => Some(
                compilation_error_to_data(&err, &self.session.source_table)
                    .into_iter()
                    .map(|data| {
                        let source_id = data.source_id;
                        data.map(|pos| {
                            self.char_index_lookup(source_id)
                                .byte_to_char_position(pos as usize)
                                as u32
                        })
                    })
                    .collect(),
            ),
        }
    }

    pub fn fn_signature(&self, name: &str) -> Option<String> {
        let module = self
            .session
            .modules()
            .get(self.user_module.module_id)
            .unwrap();
        if let Some(func) = module
            .lookup_function(name, self.session.modules())
            .ok()
            .flatten()
        {
            let module_env = ModuleEnv::new(module, self.session.modules(), false);
            Some(format!(
                "{}",
                func.definition.ty_scheme.display_rust_style(&module_env)
            ))
        } else {
            None
        }
    }

    pub fn fn_signature_without_effects(&self, name: &str) -> Option<String> {
        self.fn_signature(name)
            .as_deref()
            .map(remove_effects)
            .map(str::to_string)
    }

    pub fn run_expr(&self) -> Option<ExecutionResult> {
        self.user_module.expr.as_ref().map(|expr| {
            match expr.expr.eval(self.user_module.module_id, &self.session) {
                Ok(value) => {
                    let value = value.into_value();
                    let module = self
                        .session
                        .modules()
                        .get(self.user_module.module_id)
                        .unwrap();
                    let module_env = ModuleEnv::new(module, self.session.modules(), false);
                    let output = format!(
                        "{}: {}",
                        value.display_pretty(&expr.ty.ty),
                        expr.ty.display_rust_style(&module_env)
                    );
                    ExecutionResult::success(output)
                }
                Err(error) => {
                    let summary = error.kind.to_string();
                    let complete = format!(
                        "{}",
                        error.format_with(&(self.session.source_table(), self.session.modules()))
                    );
                    let source_id = self
                        .session
                        .source_table()
                        .get_latest_source_by_name(SRC_NAME)
                        .unwrap()
                        .0;
                    let data = ExecutionErrorData {
                        summary: summary.clone(),
                        complete,
                        data: error.top_most_location_in(source_id).map(|loc| {
                            ErrorData::from_location(loc, self.session.source_table(), summary)
                        }),
                    };
                    ExecutionResult::error(data)
                }
            }
        })
    }

    pub fn get_annotations(&mut self) -> Vec<AnnotationData> {
        let (source_id, source_entry) = match self
            .session
            .source_table()
            .get_latest_source_by_name(SRC_NAME)
        {
            Some(source) => source,
            None => return Vec::new(),
        };
        let annotations = self.user_module.display_annotations(
            source_id,
            source_entry.source(),
            &self.session,
            DisplayStyle::Rust,
        );
        let mut annotations = annotations
            .into_iter()
            .map(|(pos, hint)| {
                AnnotationData::new(
                    self.char_index_lookup(source_id).byte_to_char_position(pos),
                    hint,
                )
            })
            .collect::<Vec<_>>();
        annotations.sort_by_key(|a| a.pos);
        annotations
    }

    pub fn list_module_fn_names(&self) -> Vec<String> {
        self.list_module_fns()
            .into_iter()
            .map(|sig| sig.name)
            .collect()
    }

    pub fn list_module_fns(&self) -> Vec<FunctionSignature> {
        let mut sigs = Vec::new();
        let user_module = self
            .session
            .modules()
            .get(self.user_module.module_id)
            .unwrap();
        for (mod_name, module) in self.session.modules().iter_named() {
            for (sym_name, func) in module.iter_named_functions() {
                // skip trait methods
                if !module.is_non_trait_local_function(sym_name) {
                    continue;
                }
                if sym_name.starts_with('@') {
                    continue; // skip hidden functions
                }
                let name = if user_module.uses(mod_name, sym_name) {
                    sym_name.to_string()
                } else {
                    format!("{mod_name}::{sym_name}")
                };
                sigs.push(FunctionSignature {
                    name,
                    args: func
                        .definition
                        .arg_names
                        .iter()
                        .map(ToString::to_string)
                        .collect(),
                    doc: func.definition.doc.clone(),
                });
            }
        }
        sigs
    }

    pub fn list_module_props(&self) -> Vec<String> {
        static RE: LazyLock<Regex> = LazyLock::new(|| Regex::new(r"^@(get|set) (.*)$").unwrap());
        let mut getters = HashSet::new();
        let mut setters = HashSet::new();
        let user_module = self
            .session
            .modules()
            .get(self.user_module.module_id)
            .unwrap();
        for (mod_name, module) in self.session.modules().iter_named() {
            for (sym_name, _) in module.iter_named_functions() {
                // skip trait methods
                if !module.is_non_trait_local_function(sym_name) {
                    continue;
                }
                let captures = if let Some(captures) = RE.captures(&sym_name) {
                    captures
                } else {
                    continue; // not a property
                };
                let action = captures.get(1).unwrap().as_str();
                let name = captures.get(2).unwrap().as_str();
                let bin = match action {
                    "get" => &mut getters,
                    "set" => &mut setters,
                    _ => continue,
                };
                if user_module.uses(mod_name, sym_name) {
                    bin.insert(format!("@{name}"));
                } else {
                    bin.insert(format!("@{mod_name}::{name}"));
                }
            }
        }
        getters.intersection(&setters).cloned().collect()
    }
}

/// The compiler to be used in the web IDE, non-wasm-available part
impl Compiler {
    /* TODO: figure out how to clean that
    pub fn with_module(mut self, name: &str, module: ModuleRc, extra_uses: Uses) -> Self {
        self.modules.modules.insert(name.into(), module);
        self.extra_uses.extend(extra_uses.iter().cloned());
        self.user_module.module.uses.extend(extra_uses);
        self
    }
    */

    fn char_index_lookup(&mut self, source_id: SourceId) -> &mut CharIndexLookup {
        self.char_index_lookup.entry(source_id).or_insert_with(|| {
            CharIndexLookup::new(
                self.session
                    .source_table()
                    .get_source_text(source_id)
                    .unwrap(),
            )
        })
    }

    fn run_fn<R>(
        &self,
        name: &str,
        f: impl FnOnce(&ModuleFunction, &ModuleRc, &Modules) -> Result<R, String>,
    ) -> Result<R, String> {
        let user_module = self
            .session
            .modules()
            .get(self.user_module.module_id)
            .unwrap();
        match user_module.lookup_function(name, self.session.modules()) {
            Ok(Some(func)) => f(func, user_module, self.session.modules()),
            Ok(None) => Err(format!("Function {name} not found")),
            Err(e) => Err(format!("Lookup error for {name}: {e:?}")),
        }
    }

    pub fn run_fn_unit_unit(&self, name: &str) -> Result<(), String> {
        self.run_fn(name, |func, current, others| {
            if !func.definition.ty_scheme.is_just_type_and_effects()
                || !func.definition.ty_scheme.ty.args.is_empty()
                || func.definition.ty_scheme.ty.ret != Type::unit()
            {
                let module_env = ModuleEnv::new(current, others, false);
                Err(format!(
                    "Function {name} does not have type \"() -> ()\", it has \"{}\" instead",
                    func.definition.ty_scheme.display_rust_style(&module_env)
                ))
            } else {
                let mut ctx = EvalCtx::new(self.user_module.module_id, &self.session);
                let _ret = func
                    .code
                    .borrow()
                    .call(vec![], &mut ctx)
                    .map_err(|err| format!("Execution error: {}", err.kind))?;
                Ok(())
            }
        })
    }

    pub fn run_fn_unit_o<O: NativeValue + Clone>(&self, name: &str) -> Result<O, String> {
        self.run_fn(name, |func, current, others| {
            let o_ty = Type::primitive::<O>();
            if !func.definition.ty_scheme.is_just_type_and_effects()
                || !func.definition.ty_scheme.ty.args.is_empty()
                || func.definition.ty_scheme.ty.ret != o_ty
            {
                let module_env = ModuleEnv::new(current, others, false);
                let o_ty_fmt = o_ty.format_with(&module_env);
                Err(format!(
                    "Function {name} does not have type \"() -> {}\", it has \"{}\" instead",
                    o_ty_fmt,
                    func.definition.ty_scheme.display_rust_style(&module_env)
                ))
            } else {
                let mut ctx = EvalCtx::new(self.user_module.module_id, &self.session);
                let ret = func
                    .code
                    .borrow()
                    .call(vec![], &mut ctx)
                    .map_err(|err| format!("Execution error: {}", err.kind))?
                    .into_value();
                Ok(ret.into_primitive_ty::<O>().unwrap())
            }
        })
    }

    pub fn run_fn_unit_tuple<OA: NativeValue + Clone, OB: NativeValue + Clone>(
        &self,
        name: &str,
    ) -> Result<(OA, OB), String> {
        self.run_fn(name, |func, current, others| {
            let oa_ty = Type::primitive::<OA>();
            let ob_ty = Type::primitive::<OB>();
            let o_ty = tuple_type([oa_ty, ob_ty]);
            if !func.definition.ty_scheme.is_just_type_and_effects()
                || !func.definition.ty_scheme.ty.args.is_empty()
                || func.definition.ty_scheme.ty.ret != o_ty
            {
                let module_env = ModuleEnv::new(current, others, false);
                let o_ty_fmt = o_ty.format_with(&module_env);
                Err(format!(
                    "Function {name} does not have type \"() -> {}\", it has \"{}\" instead",
                    o_ty_fmt,
                    func.definition.ty_scheme.display_rust_style(&module_env)
                ))
            } else {
                let mut ctx = EvalCtx::new(self.user_module.module_id, &self.session);
                let ret = func
                    .code
                    .borrow()
                    .call(vec![], &mut ctx)
                    .map_err(|err| format!("Execution error: {}", err.kind))?
                    .into_value();
                let ret_tuple = ret.into_tuple().unwrap();
                let [oa, ob]: [Value; 2] = ret_tuple.into_vec().try_into().unwrap();
                let oa = oa.into_primitive_ty::<OA>().unwrap();
                let ob = ob.into_primitive_ty::<OB>().unwrap();
                Ok((oa, ob))
            }
        })
    }

    pub fn run_fn_i_tuple<
        I: NativeValue + Clone,
        OA: NativeValue + Clone,
        OB: NativeValue + Clone,
    >(
        &self,
        name: &str,
        input: I,
    ) -> Result<(OA, OB), String> {
        self.run_fn(name, |func, current, others| {
            let i_ty = Type::primitive::<I>();
            let oa_ty = Type::primitive::<OA>();
            let ob_ty = Type::primitive::<OB>();
            let o_ty = tuple_type([oa_ty, ob_ty]);
            if !func.definition.ty_scheme.is_just_type_and_effects()
                || func.definition.ty_scheme.ty.args != vec![FnArgType::new_by_val(i_ty)]
                || func.definition.ty_scheme.ty.ret != o_ty
            {
                let module_env = ModuleEnv::new(current, others, false);
                let i_ty_fmt = i_ty.format_with(&module_env);
                let o_ty_fmt = o_ty.format_with(&module_env);
                Err(format!(
                    "Function {name} does not have type \"({}) -> {}\", it has \"{}\" instead",
                    i_ty_fmt,
                    o_ty_fmt,
                    func.definition.ty_scheme.display_rust_style(&module_env)
                ))
            } else {
                let mut ctx = EvalCtx::new(self.user_module.module_id, &self.session);
                let ret = func
                    .code
                    .borrow()
                    .call(vec![ValOrMut::from_primitive(input)], &mut ctx)
                    .map_err(|err| format!("Execution error: {}", err.kind))?
                    .into_value();
                let ret_tuple = ret.into_tuple().unwrap();
                let [oa, ob]: [Value; 2] = ret_tuple.into_vec().try_into().unwrap();
                let oa = oa.into_primitive_ty::<OA>().unwrap();
                let ob = ob.into_primitive_ty::<OB>().unwrap();
                Ok((oa, ob))
            }
        })
    }

    pub fn run_fn_i_unit<I: NativeValue + Clone>(
        &self,
        name: &str,
        input: I,
    ) -> Result<(), String> {
        self.run_fn(name, |func, current, others| {
            let i_ty = Type::primitive::<I>();
            if !func.definition.ty_scheme.is_just_type_and_effects()
                || func.definition.ty_scheme.ty.args != vec![FnArgType::new_by_val(i_ty)]
                || func.definition.ty_scheme.ty.ret != Type::unit()
            {
                let module_env = ModuleEnv::new(current, others, false);
                let i_ty_fmt = i_ty.format_with(&module_env);
                Err(format!(
                    "Function {name} does not have type \"({}) -> ()\", it has \"{}\" instead",
                    i_ty_fmt,
                    func.definition.ty_scheme.display_rust_style(&module_env)
                ))
            } else {
                let mut ctx = EvalCtx::new(self.user_module.module_id, &self.session);
                let _ret = func
                    .code
                    .borrow()
                    .call(vec![ValOrMut::from_primitive(input)], &mut ctx)
                    .map_err(|err| format!("Execution error: {}", err.kind))?;
                Ok(())
            }
        })
    }

    pub fn run_fn_i_o<I: NativeValue + Clone, O: NativeValue + Clone>(
        &self,
        name: &str,
        input: I,
    ) -> Result<O, String> {
        self.run_fn(name, |func, current, others| {
            let i_ty = Type::primitive::<I>();
            let o_ty = Type::primitive::<O>();
            if !func.definition.ty_scheme.is_just_type_and_effects()
                || func.definition.ty_scheme.ty.args != vec![FnArgType::new_by_val(i_ty)]
                || func.definition.ty_scheme.ty.ret != o_ty
            {
                let module_env = ModuleEnv::new(current, others, false);
                let i_ty_fmt = i_ty.format_with(&module_env);
                let o_ty_fmt = o_ty.format_with(&module_env);
                Err(format!(
                    "Function {name} does not have type \"({}) -> {}\", it has \"{}\" instead",
                    i_ty_fmt,
                    o_ty_fmt,
                    func.definition.ty_scheme.display_rust_style(&module_env)
                ))
            } else {
                let mut ctx = EvalCtx::new(self.user_module.module_id, &self.session);
                let ret = func
                    .code
                    .borrow()
                    .call(vec![ValOrMut::from_primitive(input)], &mut ctx)
                    .map_err(|err| format!("Execution error: {}", err.kind))?
                    .into_value();
                Ok(ret.into_primitive_ty::<O>().unwrap())
            }
        })
    }
}

impl Default for Compiler {
    fn default() -> Self {
        Compiler::new()
    }
}

fn remove_effects(signature: &str) -> &str {
    match signature.rsplit_once("!") {
        // If "!" is found, return the part before it (removing the effects)
        Some((before_effects, _)) => before_effects.trim(),
        // If "!" is not found, return the original string (no effects to remove)
        None => signature.trim(),
    }
}

#[cfg(test)]
mod tests {
    use crate::std::string::String as Str;
    use std::str::FromStr;

    use crate::containers::iterable_to_string;

    use super::*;

    fn build(code: &str) -> Compiler {
        let mut compiler = Compiler::new();
        let errors = compiler.compile(code);
        if let Some(errors) = errors {
            panic!("Compilation errors: {}", iterable_to_string(&errors, ", "));
        }
        compiler
    }

    #[test]
    fn compiler_has_some_std_fns() {
        let compiler = Compiler::new();
        let names = compiler.list_module_fn_names();
        assert!(names.contains(&"string_len".to_string()));
    }

    #[test]
    fn run_fn_unit_unit() {
        let compiler = build("fn main() { () }");
        compiler.run_fn_unit_unit("main").expect("Execution failed");
    }

    #[test]
    fn run_fn_unit_int() {
        let compiler = build("fn main() -> int { 42 }");
        let result = compiler
            .run_fn_unit_o::<isize>("main")
            .expect("Execution failed");
        assert_eq!(result, 42);
    }

    #[test]
    fn run_fn_int_unit() {
        let compiler = build("fn main(x: int) { }");
        compiler
            .run_fn_i_unit("main", 42)
            .expect("Execution failed");
    }

    #[test]
    fn run_fn_int_int() {
        let compiler = build("fn main(x) -> int { x + 1 }");
        let result = compiler
            .run_fn_i_o::<_, isize>("main", 1)
            .expect("Execution failed");
        assert_eq!(result, 2);
    }

    #[test]
    fn run_fn_string_int() {
        let compiler = build("fn main(x) { string_len(x) }");
        let input = Str::from_str("hi world").unwrap();
        let result = compiler
            .run_fn_i_o::<_, isize>("main", input)
            .expect("Execution failed");
        assert_eq!(result, 8);
    }

    #[test]
    fn run_fn_unit_tuple() {
        let compiler = build("fn main() { (true, 43) }");
        let result = compiler
            .run_fn_unit_tuple::<bool, isize>("main")
            .expect("Execution failed");
        assert_eq!(result, (true, 43));
    }

    #[test]
    fn run_fn_int_tuple() {
        let compiler = build("fn main(x) { (true, (x+1: int)) }");
        let result = compiler
            .run_fn_i_tuple::<isize, bool, isize>("main", 42)
            .expect("Execution failed");
        assert_eq!(result, (true, 43));
    }

    #[test]
    fn fn_signature() {
        let compiler = build("fn main(x) { string_len(x) }");
        let signature = compiler.fn_signature("main").unwrap();
        assert_eq!(signature, "(string) -> int");
    }
}
