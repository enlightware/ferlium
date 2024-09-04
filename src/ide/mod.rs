use std::fmt::{self, Display};

use crate::{
    compile,
    eval::{EvalCtx, ValOrMut},
    module::{FmtWithModuleEnv, Uses},
    r#type::{FnType, Type},
    std::new_std_module_env,
    std::string::String as Str,
    value::NativeValue,
    CompilationError, DisplayStyle, Module, ModuleAndExpr, ModuleEnv, Modules, Span,
};
use ustr::ustr;
#[cfg(target_arch = "wasm32")]
use wasm_bindgen::prelude::*;

mod char_index_lookup;
use char_index_lookup::CharIndexLookup;

/// An error-data structure to be used in IDEs
#[cfg_attr(target_arch = "wasm32", wasm_bindgen(getter_with_clone))]
pub struct ErrorData {
    pub from: usize,
    pub to: usize,
    pub text: String,
}

#[cfg_attr(target_arch = "wasm32", wasm_bindgen)]
impl ErrorData {
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen(constructor))]
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

impl Display for ErrorData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.text)
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
        WrongNumberOfArguments {
            expected,
            expected_span,
            got,
            got_span,
        } => vec![
            ErrorData::from_span(
                expected_span,
                format!("Expected {expected} arguments here, got {got}"),
            ),
            ErrorData::from_span(
                got_span,
                format!("Expected {expected} arguments, got {got} here"),
            ),
        ],
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
            first_occurrence,
            second_occurrence,
        } => {
            let name = &src[first_occurrence.start()..first_occurrence.end()];
            vec![
                ErrorData::from_span(first_occurrence, format!("Duplicated field {name}")),
                ErrorData::from_span(second_occurrence, format!("Duplicated field {name}")),
            ]
        }
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
        InvalidVariantName { name, ty } => {
            let name_text = &src[name.start()..name.end()];
            vec![ErrorData::from_span(
                name,
                format!("Variant name {name_text} does not exist for variant type {ty}"),
            )]
        }
        InvalidVariantType { name, ty } => {
            let name_text = &src[name.start()..name.end()];
            vec![ErrorData::from_span(
                name,
                format!(
                    "Type {ty} is not a variant, but variant constructor {name_text} requires it"
                ),
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
        InconsistentPattern {
            a_type,
            a_span,
            b_type,
            b_span,
        } => {
            let a_name = a_type.name();
            let b_name = b_type.name();
            vec![
                ErrorData::from_span(
                    a_span,
                    format!("Pattern expects {a_name}, but got {b_name}"),
                ),
                ErrorData::from_span(
                    b_span,
                    format!("Pattern expects {b_name}, but got {a_name}"),
                ),
            ]
        }
        DuplicatedVariant {
            first_occurrence,
            second_occurrence,
        } => {
            let name = &src[first_occurrence.start()..first_occurrence.end()];
            let text = format!("Duplicated variant {name}");
            vec![
                ErrorData::from_span(first_occurrence, text.clone()),
                ErrorData::from_span(second_occurrence, text),
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
            var_span,
            string_span,
        } => {
            let var_text = &src[var_span.start()..var_span.end()];
            let string_text = &src[string_span.start()..string_span.end()];
            vec![ErrorData::from_span(
                var_span,
                format!("Undefined variable {var_text} used in string formatting: {string_text}"),
            )]
        }
        Internal(msg) => vec![ErrorData::from_span(
            &Span::new(0, 0),
            format!("ICE: {msg}"),
        )],
    }
}

/// An annotation data structer to be used in IDEs
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

#[derive(Default)]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen)]
pub struct Compiler {
    modules: Modules,
    extra_uses: Uses,
    user_src: String,
    user_module: ModuleAndExpr,
}

/// The compiler to be used in the web IDE, wasm-available part
#[cfg_attr(target_arch = "wasm32", wasm_bindgen)]
impl Compiler {
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen(constructor))]
    pub fn new() -> Self {
        Self {
            modules: new_std_module_env(),
            ..Default::default()
        }
    }

    fn compile_internal(&mut self, src: &str) -> Result<(), CompilationError> {
        self.user_module = compile(src, &self.modules, &self.extra_uses)?;
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

    #[cfg_attr(target_arch = "wasm32", wasm_bindgen(skip))]
    pub fn run_fn_unit_o<O: NativeValue + Clone>(&self, name: &str) -> Result<O, String> {
        if let Some(func) = self
            .user_module
            .module
            .get_function(ustr(name), &self.modules)
        {
            let module_env = ModuleEnv::new(&self.user_module.module, &self.modules);
            let o_ty = Type::primitive::<O>();
            let o_ty_fmt = o_ty.format_with(&module_env);
            if !func.ty_scheme.is_just_type() || func.ty_scheme.ty != FnType::new_by_val(&[], o_ty)
            {
                Err(format!(
                    "Function {name} does not have type \"() -> {}\", it has \"{}\" instead",
                    o_ty_fmt,
                    func.ty_scheme.display_rust_style(&module_env)
                ))
            } else {
                let mut ctx = EvalCtx::new();
                let ret = func
                    .code
                    .borrow()
                    .call(vec![], &mut ctx)
                    .map_err(|err| format!("Execution error: {err}"))?;
                ret.into_primitive_ty::<O>()
                    .ok_or(format!("Function did not return an {}", o_ty_fmt))
            }
        } else {
            Err(format!("Function {name} not found"))
        }
    }

    #[cfg_attr(target_arch = "wasm32", wasm_bindgen(skip))]
    pub fn run_fn_i_o<I: NativeValue + Clone, O: NativeValue + Clone>(
        &self,
        name: &str,
        input: I,
    ) -> Result<O, String> {
        if let Some(func) = self
            .user_module
            .module
            .get_function(ustr(name), &self.modules)
        {
            let module_env = ModuleEnv::new(&self.user_module.module, &self.modules);
            let i_ty = Type::primitive::<I>();
            let i_ty_fmt = i_ty.format_with(&module_env);
            let o_ty = Type::primitive::<O>();
            let o_ty_fmt = o_ty.format_with(&module_env);
            if !func.ty_scheme.is_just_type()
                || func.ty_scheme.ty != FnType::new_by_val(&[i_ty], o_ty)
            {
                let module_env = ModuleEnv::new(&self.user_module.module, &self.modules);
                Err(format!(
                    "Function {name} does not have type \"({}) -> {}\", it has \"{}\" instead",
                    i_ty_fmt,
                    o_ty_fmt,
                    func.ty_scheme.display_rust_style(&module_env)
                ))
            } else {
                let mut ctx = EvalCtx::new();
                let ret = func
                    .code
                    .borrow()
                    .call(vec![ValOrMut::from_primitive(input)], &mut ctx)
                    .map_err(|err| format!("Execution error: {err}"))?;
                ret.into_primitive_ty::<O>()
                    .ok_or(format!("Function did not return an {}", o_ty_fmt))
            }
        } else {
            Err(format!("Function {name} not found"))
        }
    }

    pub fn run_expr_to_html(&self) -> String {
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

/// The compiler to be used in the web IDE, non-wasm-available part
impl Compiler {
    pub fn with_module(mut self, name: &str, module: Module, extra_uses: Uses) -> Self {
        self.modules.insert(name.into(), module);
        self.extra_uses.extend(extra_uses);
        self
    }
}

#[cfg(test)]
mod tests {
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
    fn run_fn_unit_int() {
        let compiler = build("fn main() { 42 }");
        let result = compiler
            .run_fn_unit_o::<isize>("main")
            .expect("Execution failed");
        assert_eq!(result, 42);
    }

    #[test]
    fn run_fn_int_int() {
        let compiler = build("fn main(x) { x+1 }");
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
}
