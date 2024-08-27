mod utils;

use painturscript::{
    compile,
    error::CompilationError,
    module::{ModuleEnv, Modules},
    std::new_std_module_env,
    type_scheme::DisplayStyle,
    ModuleAndExpr, Span,
};
use utils::{set_panic_hook, CharIndexLookup};
use wasm_bindgen::prelude::*;

/// An error-data structure to be used in IDEs
#[wasm_bindgen(getter_with_clone)]
pub struct ErrorData {
    pub from: usize,
    pub to: usize,
    pub text: String,
}

#[wasm_bindgen]
impl ErrorData {
    #[wasm_bindgen(constructor)]
    pub fn new(from: usize, to: usize, text: String) -> Self {
        Self { from, to, text }
    }
    fn from_span(span: &Span, text: String) -> Self {
        Self {
            from: span.start(),
            to: span.end(),
            text,
        }
    }
    pub(crate) fn map(self, f: impl Fn(usize) -> usize) -> Self {
        Self {
            from: f(self.from),
            to: f(self.to),
            text: self.text,
        }
    }
}

fn compilation_error_to_data(error: &CompilationError, src: &str) -> Vec<ErrorData> {
    use CompilationError::*;
    match error {
        ParsingFailed(errors) => errors
            .iter()
            .map(|(msg, span)| ErrorData::from_span(span, msg.clone()))
            .collect(),
        VariableNotFound(name, span) => vec![ErrorData::from_span(
            span,
            format!("Variable {name} not found"),
        )],
        FunctionNotFound(name, span) => vec![ErrorData::from_span(
            span,
            format!("Function {name} not found"),
        )],
        MustBeMutable(cur_span, _reason_span) => vec![ErrorData::from_span(
            cur_span,
            "Expression must be mutable".to_string(),
        )],
        IsNotSubtype(cur, cur_span, exp, _exp_span) => vec![ErrorData::from_span(
            cur_span,
            format!("Type {cur} is incompatible with type {exp}"),
        )],
        InfiniteType(ty_var, ty, span) => vec![ErrorData::from_span(
            span,
            format!("Infinite type: {ty_var} = {ty}"),
        )],
        UnboundTypeVar { ty_var, ty, span } => vec![ErrorData::from_span(
            span,
            format!("Unbound type variable {ty_var} in {ty}"),
        )],
        InvalidTupleIndex {
            index,
            index_span,
            tuple_length,
            ..
        } => vec![ErrorData::from_span(
            index_span,
            format!("Invalid index {index} of a tuple of length {tuple_length}"),
        )],
        InvalidTupleProjection {
            expr_ty,
            expr_span,
            index_span,
        } => {
            let index_name = &src[index_span.start()..index_span.end()];
            vec![ErrorData::from_span(
                expr_span,
                format!("Expected tuple because of .{index_name}, got {expr_ty}"),
            )]
        }
        DuplicatedRecordField {
            name,
            first_occurrence_span,
            second_occurrence_span,
        } => vec![
            ErrorData::from_span(first_occurrence_span, format!("Duplicated field {name}")),
            ErrorData::from_span(second_occurrence_span, format!("Duplicated field {name}")),
        ],
        InvalidRecordField {
            field_span,
            record_ty,
            ..
        } => {
            let field_name = &src[field_span.start()..field_span.end()];
            vec![ErrorData::from_span(
                field_span,
                format!("Field {field_name} not found in record {record_ty}"),
            )]
        }
        InvalidRecordFieldAccess {
            field_span,
            record_ty,
            ..
        } => {
            let field_name = &src[field_span.start()..field_span.end()];
            vec![ErrorData::from_span(
                field_span,
                format!("Expected record because of .{field_name}, got {record_ty}"),
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
                ErrorData::from_span(
                    a_span,
                    format!("Data type {a_name} here is different than data type {b_name}"),
                ),
                ErrorData::from_span(
                    b_span,
                    format!("Data type {b_name} here is different than data type {a_name}"),
                ),
            ]
        }
        MutablePathsOverlap {
            a_span,
            b_span,
            fn_span,
        } => {
            let a_name = &src[a_span.start()..a_span.end()];
            let b_name = &src[b_span.start()..b_span.end()];
            let fn_name = &src[fn_span.start()..fn_span.end()];
            vec![
                ErrorData::from_span(a_span, format!("Mutable path {a_name} (here) overlaps with {b_name} when calling function {fn_name}")),
                ErrorData::from_span(b_span, format!("Mutable path {a_name} overlaps with {b_name} (here) when calling function {fn_name}")),
                ErrorData::from_span(fn_span, format!("When calling function {fn_name}: mutable path {a_name} overlaps with {b_name}")),
            ]
        }
        UndefinedVarInStringFormatting {
            var_name,
            var_span,
            string_span,
        } => {
            let string_text = &src[string_span.start()..string_span.end()];
            vec![ErrorData::from_span(
                var_span,
                format!("Undefined variable {var_name} used in string formatting: {string_text}"),
            )]
        }
        Internal(msg) => vec![ErrorData::from_span(
            &Span::new(0, 0),
            format!("ICE: {msg}"),
        )],
    }
}

/// An annotation data structer to be used in IDEs
#[wasm_bindgen(getter_with_clone)]
pub struct AnnotationData {
    pub pos: usize,
    pub hint: String,
}

#[wasm_bindgen]
impl AnnotationData {
    #[wasm_bindgen(constructor)]
    pub fn new(pos: usize, hint: String) -> Self {
        Self { pos, hint }
    }
}

#[derive(Default)]
#[wasm_bindgen]
struct Compiler {
    modules: Modules,
    user_src: String,
    user_module: ModuleAndExpr,
}

#[wasm_bindgen]
impl Compiler {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        Self {
            modules: new_std_module_env(),
            ..Default::default()
        }
    }

    fn compile_internal(&mut self, src: &str) -> Result<(), CompilationError> {
        self.user_module = compile(src, &self.modules)?;
        self.user_src = src.to_string();
        Ok(())
    }

    pub fn compile(&mut self, src: &str) -> Option<Vec<ErrorData>> {
        let char_indices = CharIndexLookup::new(src);
        match self.compile_internal(src) {
            Ok(()) => None,
            Err(err) => Some(
                compilation_error_to_data(&err, src)
                    .into_iter()
                    .map(|data| data.map(|pos| char_indices.byte_to_char_position(pos)))
                    .collect(),
            ),
        }
    }

    pub fn run(&self) -> String {
        if let Some(expr) = &self.user_module.expr {
            match expr.expr.eval() {
                Ok(value) => {
                    let module_env = ModuleEnv::new(&self.user_module.module, &self.modules);
                    let output = format!("{}: {}", value, expr.ty.display_rust_style(&module_env));
                    html_escape::encode_text(&output).to_string()
                }
                Err(err) => {
                    let text = format!("{err}");
                    format!(
                        "<span class=\"error\">{}</span>",
                        html_escape::encode_text(&text)
                    )
                }
            }
        } else {
            "<span class=\"warning\">No expression to run</span>".to_string()
        }
    }

    pub fn get_annotations(&self) -> Vec<AnnotationData> {
        let char_indices = CharIndexLookup::new(&self.user_src);
        let mut annotations = self
            .user_module
            .display_annotations(self.user_src.as_str(), &self.modules, DisplayStyle::Rust)
            .iter()
            .map(|(pos, hint)| {
                AnnotationData::new(char_indices.byte_to_char_position(*pos), hint.clone())
            })
            .collect::<Vec<_>>();
        annotations.sort_by_key(|a| a.pos);
        annotations
    }
}

#[wasm_bindgen]
pub fn init_rust_api() {
    set_panic_hook();
    wasm_logger::init(wasm_logger::Config::default());
    log::info!("Rust API logging enabled.");
}
