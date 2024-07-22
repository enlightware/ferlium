mod utils;

use painturscript::{
    compile, error::CompilationError, module::Modules, std::new_std_module_env, type_scheme::DisplayStyle, ModuleAndExpr, Span
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

fn compilation_error_to_data(error: &CompilationError) -> Vec<ErrorData> {
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
        TypeMismatch(a, b, span) => vec![ErrorData::from_span(
            span,
            format!("Type {a} is incompatible with type {b}"),
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
            expr_ty, expr_span, ..
        } => vec![ErrorData::from_span(
            expr_span,
            format!("Expected tuple, got {expr_ty}"),
        )],
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
                compilation_error_to_data(&err)
                    .into_iter()
                    .map(|data| data.map(|pos| char_indices.byte_to_char_position(pos)))
                    .collect(),
            ),
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
