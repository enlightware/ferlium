// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{
    borrow::Cow,
    collections::HashSet,
    fmt::{self, Display},
    ops::Deref,
    rc::Rc,
    sync::LazyLock,
};

use crate::{
    compile,
    error::{CompilationErrorImpl, MutabilityMustBeWhat},
    eval::{EvalCtx, ValOrMut},
    module::{FmtWithModuleEnv, ModuleFunction, Uses},
    r#type::{FnArgType, Type},
    std::{new_module_with_prelude, new_std_module_env},
    value::{NativeValue, Value},
    CompilationError, DisplayStyle, Location, Module, ModuleAndExpr, ModuleEnv, Modules,
};
use regex::Regex;
#[cfg(target_arch = "wasm32")]
use wasm_bindgen::prelude::*;

mod annotations;
mod char_index_lookup;
use char_index_lookup::{get_line_column, CharIndexLookup};

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
    fn from_location(loc: &Location, text: String) -> Self {
        Self {
            from: loc.start(),
            to: loc.end(),
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

/// A function signature data struct to be used in IDEs
#[cfg_attr(target_arch = "wasm32", wasm_bindgen(getter_with_clone))]
pub struct FunctionSignature {
    pub name: String,
    pub args: Vec<String>,
    pub doc: Option<String>,
}

fn compilation_error_to_data(
    error: &CompilationError,
    src: &str,
    modules: &Modules,
) -> Vec<ErrorData> {
    let fmt_span = |span: &Location| match span.module() {
        None => Cow::from(&src[span.start()..span.end()]),
        Some(module) => Cow::from(
            match modules
                .get(&module.module_name())
                .and_then(|module| module.source.as_deref())
            {
                Some(src) => {
                    let position = get_line_column(src, module.span().start());
                    format!(
                        "{} (in {}:{}:{})",
                        &src[module.span().start()..module.span().end()],
                        module.module_name(),
                        position.0,
                        position.1,
                    )
                }
                None => format!(
                    "{}..{} in unknown module {}",
                    module.span().start(),
                    module.span().end(),
                    module.module_name(),
                ),
            },
        ),
    };
    use CompilationErrorImpl::*;
    match error.deref() {
        ParsingFailed(errors) => errors
            .iter()
            .map(|(msg, span)| ErrorData::from_location(span, msg.clone()))
            .collect(),
        VariableNotFound(span) => vec![ErrorData::from_location(
            span,
            format!("Variable {} not found", fmt_span(span)),
        )],
        FunctionNotFound(span) => vec![ErrorData::from_location(
            span,
            format!("Function {} not found", fmt_span(span)),
        )],
        WrongNumberOfArguments {
            expected,
            expected_span,
            got,
            got_span,
        } => vec![
            ErrorData::from_location(
                expected_span,
                format!("Expected {expected} arguments here, got {got}"),
            ),
            ErrorData::from_location(
                got_span,
                format!("Expected {expected} arguments, got {got} here"),
            ),
        ],
        MutabilityMustBe {
            source_span,
            reason_span,
            what,
            ..
        } => vec![ErrorData::from_location(source_span, {
            use MutabilityMustBeWhat::*;
            match what {
                Mutable => format!(
                    "Expression must be mutable due to {}",
                    fmt_span(reason_span)
                ),
                Constant => format!(
                    "Expression must be constant due to {}",
                    fmt_span(reason_span)
                ),
                Equal => format!(
                    "Expression must be of the same mutability as {}",
                    fmt_span(reason_span)
                ),
            }
        })],
        TypeMismatch {
            current_ty,
            current_span,
            expected_ty,
            ..
        } => vec![ErrorData::from_location(
            current_span,
            format!("Type {current_ty} is incompatible with type {expected_ty}"),
        )],
        InfiniteType(ty_var, ty, span) => vec![ErrorData::from_location(
            span,
            format!("Infinite type: {ty_var} = {ty}"),
        )],
        UnboundTypeVar { ty_var, ty, span } => vec![ErrorData::from_location(
            span,
            format!("Unbound type variable {ty_var} in {ty}"),
        )],
        InvalidTupleIndex {
            index,
            index_span,
            tuple_length,
            ..
        } => vec![ErrorData::from_location(
            index_span,
            format!("Invalid index {index} of a tuple of length {tuple_length}"),
        )],
        InvalidTupleProjection {
            expr_ty,
            expr_span,
            index_span,
        } => {
            let index_name = fmt_span(index_span);
            vec![ErrorData::from_location(
                expr_span,
                format!("Expected tuple because of .{index_name}, got {expr_ty}"),
            )]
        }
        DuplicatedRecordField {
            first_occurrence,
            second_occurrence,
        } => {
            let name = fmt_span(first_occurrence);
            vec![
                ErrorData::from_location(first_occurrence, format!("Duplicated field {name}")),
                ErrorData::from_location(second_occurrence, format!("Duplicated field {name}")),
            ]
        }
        InvalidRecordField {
            field_span,
            record_ty,
            ..
        } => {
            let field_name = fmt_span(field_span);
            vec![ErrorData::from_location(
                field_span,
                format!("Field {field_name} not found in record {record_ty}"),
            )]
        }
        InvalidRecordFieldAccess {
            field_span,
            record_ty,
            ..
        } => {
            let field_name = fmt_span(field_span);
            vec![ErrorData::from_location(
                field_span,
                format!("Expected record because of .{field_name}, got {record_ty}"),
            )]
        }
        InvalidVariantName { name, ty, valids } => {
            let name_text = fmt_span(name);
            vec![ErrorData::from_location(
                name,
                format!("Variant name {name_text} does not exist for variant type {ty}, valid names are {}", valids.join(", ")),
            )]
        }
        InvalidVariantType { name, ty } => {
            let name_text = fmt_span(name);
            vec![ErrorData::from_location(
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
                ErrorData::from_location(
                    a_span,
                    format!("Data type {a_name} here is different than data type {b_name}"),
                ),
                ErrorData::from_location(
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
                ErrorData::from_location(
                    a_span,
                    format!("Pattern expects {a_name}, but got {b_name}"),
                ),
                ErrorData::from_location(
                    b_span,
                    format!("Pattern expects {b_name}, but got {a_name}"),
                ),
            ]
        }
        DuplicatedVariant {
            first_occurrence,
            second_occurrence,
        } => {
            let name = fmt_span(first_occurrence);
            let text = format!("Duplicated variant {name}");
            vec![
                ErrorData::from_location(first_occurrence, text.clone()),
                ErrorData::from_location(second_occurrence, text),
            ]
        }
        TraitImplNotFound {
            trait_name,
            input_tys,
            fn_span,
        } => {
            vec![ErrorData::from_location(
                fn_span,
                format!(
                    "Implementation of trait {trait_name} over types {} not found",
                    input_tys.join(", ")
                ),
            )]
        }
        IdentifierBoundMoreThanOnceInAPattern {
            first_occurrence,
            second_occurrence,
        } => {
            let name_text = fmt_span(first_occurrence);
            let text = format!("Identifier {name_text} bound more than once in a pattern");
            vec![
                ErrorData::from_location(first_occurrence, text.clone()),
                ErrorData::from_location(second_occurrence, text),
            ]
        }
        DuplicatedLiteralPattern {
            first_occurrence,
            second_occurrence,
        } => {
            let name_text = fmt_span(first_occurrence);
            let text = format!("Duplicated literal pattern {name_text}");
            vec![
                ErrorData::from_location(first_occurrence, text.clone()),
                ErrorData::from_location(second_occurrence, text),
            ]
        }
        EmptyMatchBody { span } => vec![ErrorData::from_location(
            span,
            "Match body cannot be empty".to_string(),
        )],
        NonExhaustivePattern { span, ty } => {
            vec![ErrorData::from_location(
                span,
                format!(
                    "Non-exhaustive patterns for type {ty}, all possible values must be covered."
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
                ErrorData::from_location(a_span, format!("Mutable path {a_name} (here) overlaps with {b_name} when calling function {fn_name}")),
                ErrorData::from_location(b_span, format!("Mutable path {a_name} overlaps with {b_name} (here) when calling function {fn_name}")),
                ErrorData::from_location(fn_span, format!("When calling function {fn_name}: mutable path {a_name} overlaps with {b_name}")),
            ]
        }
        UndefinedVarInStringFormatting {
            var_span,
            string_span,
        } => {
            let var_text = fmt_span(var_span);
            let string_text = fmt_span(string_span);
            vec![ErrorData::from_location(
                var_span,
                format!("Undefined variable {var_text} used in string formatting: {string_text}"),
            )]
        }
        InvalidEffectDependency {
            source,
            source_span,
            target,
            ..
        } => {
            vec![ErrorData::from_location(
                source_span,
                format!("Effect {source} cannot depend on {target}"),
            )]
        }
        UnknownProperty {
            scope,
            variable,
            span,
            ..
        } => {
            vec![ErrorData::from_location(
                span,
                format!("Unknown property {scope}.{variable}"),
            )]
        }
        Unsupported { span, reason } => vec![ErrorData::from_location(span, reason.to_string())],
        Internal(msg) => vec![ErrorData::from_location(
            &Location::new_local(0, 0),
            format!("ICE: {msg}"),
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
            user_module: ModuleAndExpr::new_just_module(new_module_with_prelude()),
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
                compilation_error_to_data(&err, src, &self.modules)
                    .into_iter()
                    .map(|data| data.map(|pos| char_indices.byte_to_char_position(pos)))
                    .collect(),
            ),
        }
    }

    pub fn fn_signature(&self, name: &str) -> Option<String> {
        if let Some(func) = self.user_module.module.get_function(name, &self.modules) {
            let module_env = ModuleEnv::new(&self.user_module.module, &self.modules);
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

    pub fn list_module_fn_names(&self) -> Vec<String> {
        self.list_module_fns()
            .into_iter()
            .map(|sig| sig.name)
            .collect()
    }

    pub fn list_module_fns(&self) -> Vec<FunctionSignature> {
        let mut sigs = Vec::new();
        for module in &self.modules {
            let mod_name = *module.0;
            for (sym_name, func) in &module.1.functions {
                if sym_name.starts_with('@') {
                    continue; // skip hidden functions
                }
                let name = if self.user_module.module.uses(mod_name, *sym_name) {
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
        for module in &self.modules {
            let mod_name = *module.0;
            for f in &module.1.functions {
                let sym_name = *f.0;
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
                if self.user_module.module.uses(mod_name, sym_name) {
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
    pub fn new_with_modules(modules: Modules, extra_uses: Uses) -> Self {
        let user_src = String::new();
        let mut user_module = ModuleAndExpr::new_just_module(new_module_with_prelude());
        user_module.module.uses.extend(extra_uses.iter().cloned());
        Self {
            modules,
            extra_uses,
            user_src,
            user_module,
        }
    }

    pub fn with_module(mut self, name: &str, module: Module, extra_uses: Uses) -> Self {
        self.modules.insert(name.into(), Rc::new(module));
        self.extra_uses.extend(extra_uses.iter().cloned());
        self.user_module.module.uses.extend(extra_uses);
        self
    }

    fn run_fn<R>(
        &self,
        name: &str,
        f: impl FnOnce(&ModuleFunction, &ModuleEnv<'_>) -> Result<R, String>,
    ) -> Result<R, String> {
        if let Some(func) = self.user_module.module.get_function(name, &self.modules) {
            let module_env = ModuleEnv::new(&self.user_module.module, &self.modules);
            f(func, &module_env)
        } else {
            Err(format!("Function {name} not found"))
        }
    }

    pub fn run_fn_unit_unit(&self, name: &str) -> Result<(), String> {
        self.run_fn(name, |func, module_env| {
            if !func.definition.ty_scheme.is_just_type_and_effects()
                || !func.definition.ty_scheme.ty.args.is_empty()
                || func.definition.ty_scheme.ty.ret != Type::unit()
            {
                Err(format!(
                    "Function {name} does not have type \"() -> ()\", it has \"{}\" instead",
                    func.definition.ty_scheme.display_rust_style(module_env)
                ))
            } else {
                let mut ctx = EvalCtx::new();
                let _ret = func
                    .code
                    .borrow()
                    .call(vec![], &mut ctx)
                    .map_err(|err| format!("Execution error: {err}"))?;
                Ok(())
            }
        })
    }

    pub fn run_fn_unit_o<O: NativeValue + Clone>(&self, name: &str) -> Result<O, String> {
        self.run_fn(name, |func, module_env| {
            let o_ty = Type::primitive::<O>();
            let o_ty_fmt = o_ty.format_with(module_env);
            if !func.definition.ty_scheme.is_just_type_and_effects()
                || !func.definition.ty_scheme.ty.args.is_empty()
                || func.definition.ty_scheme.ty.ret != o_ty
            {
                Err(format!(
                    "Function {name} does not have type \"() -> {}\", it has \"{}\" instead",
                    o_ty_fmt,
                    func.definition.ty_scheme.display_rust_style(module_env)
                ))
            } else {
                let mut ctx = EvalCtx::new();
                let ret = func
                    .code
                    .borrow()
                    .call(vec![], &mut ctx)
                    .map_err(|err| format!("Execution error: {err}"))?;
                Ok(ret.into_primitive_ty::<O>().unwrap())
            }
        })
    }

    pub fn run_fn_unit_tuple<OA: NativeValue + Clone, OB: NativeValue + Clone>(
        &self,
        name: &str,
    ) -> Result<(OA, OB), String> {
        self.run_fn(name, |func, module_env| {
            let oa_ty = Type::primitive::<OA>();
            let ob_ty = Type::primitive::<OB>();
            let o_ty = Type::tuple(vec![oa_ty, ob_ty]);
            let o_ty_fmt = o_ty.format_with(module_env);
            if !func.definition.ty_scheme.is_just_type_and_effects()
                || !func.definition.ty_scheme.ty.args.is_empty()
                || func.definition.ty_scheme.ty.ret != o_ty
            {
                Err(format!(
                    "Function {name} does not have type \"() -> {}\", it has \"{}\" instead",
                    o_ty_fmt,
                    func.definition.ty_scheme.display_rust_style(module_env)
                ))
            } else {
                let mut ctx = EvalCtx::new();
                let ret = func
                    .code
                    .borrow()
                    .call(vec![], &mut ctx)
                    .map_err(|err| format!("Execution error: {err}"))?;
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
        self.run_fn(name, |func, module_env| {
            let i_ty = Type::primitive::<I>();
            let i_ty_fmt = i_ty.format_with(module_env);
            let oa_ty = Type::primitive::<OA>();
            let ob_ty = Type::primitive::<OB>();
            let o_ty = Type::tuple(vec![oa_ty, ob_ty]);
            let o_ty_fmt = o_ty.format_with(module_env);
            if !func.definition.ty_scheme.is_just_type_and_effects()
                || func.definition.ty_scheme.ty.args != vec![FnArgType::new_by_val(i_ty)]
                || func.definition.ty_scheme.ty.ret != o_ty
            {
                Err(format!(
                    "Function {name} does not have type \"({}) -> {}\", it has \"{}\" instead",
                    i_ty_fmt,
                    o_ty_fmt,
                    func.definition.ty_scheme.display_rust_style(module_env)
                ))
            } else {
                let mut ctx = EvalCtx::new();
                let ret = func
                    .code
                    .borrow()
                    .call(vec![ValOrMut::from_primitive(input)], &mut ctx)
                    .map_err(|err| format!("Execution error: {err}"))?;
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
        self.run_fn(name, |func, module_env| {
            let i_ty = Type::primitive::<I>();
            let i_ty_fmt = i_ty.format_with(module_env);
            if !func.definition.ty_scheme.is_just_type_and_effects()
                || func.definition.ty_scheme.ty.args != vec![FnArgType::new_by_val(i_ty)]
                || func.definition.ty_scheme.ty.ret != Type::unit()
            {
                Err(format!(
                    "Function {name} does not have type \"({}) -> ()\", it has \"{}\" instead",
                    i_ty_fmt,
                    func.definition.ty_scheme.display_rust_style(module_env)
                ))
            } else {
                let mut ctx = EvalCtx::new();
                let _ret = func
                    .code
                    .borrow()
                    .call(vec![ValOrMut::from_primitive(input)], &mut ctx)
                    .map_err(|err| format!("Execution error: {err}"))?;
                Ok(())
            }
        })
    }

    pub fn run_fn_i_o<I: NativeValue + Clone, O: NativeValue + Clone>(
        &self,
        name: &str,
        input: I,
    ) -> Result<O, String> {
        self.run_fn(name, |func, module_env| {
            let i_ty = Type::primitive::<I>();
            let i_ty_fmt = i_ty.format_with(module_env);
            let o_ty = Type::primitive::<O>();
            let o_ty_fmt = o_ty.format_with(module_env);
            if !func.definition.ty_scheme.is_just_type_and_effects()
                || func.definition.ty_scheme.ty.args != vec![FnArgType::new_by_val(i_ty)]
                || func.definition.ty_scheme.ty.ret != o_ty
            {
                Err(format!(
                    "Function {name} does not have type \"({}) -> {}\", it has \"{}\" instead",
                    i_ty_fmt,
                    o_ty_fmt,
                    func.definition.ty_scheme.display_rust_style(module_env)
                ))
            } else {
                let mut ctx = EvalCtx::new();
                let ret = func
                    .code
                    .borrow()
                    .call(vec![ValOrMut::from_primitive(input)], &mut ctx)
                    .map_err(|err| format!("Execution error: {err}"))?;
                Ok(ret.into_primitive_ty::<O>().unwrap())
            }
        })
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
        let compiler = build("fn main() { 42 }");
        let result = compiler
            .run_fn_unit_o::<isize>("main")
            .expect("Execution failed");
        assert_eq!(result, 42);
    }

    #[test]
    fn run_fn_int_unit() {
        let compiler = build("fn main(x) { let a = x + 0; () }");
        compiler
            .run_fn_i_unit("main", 42)
            .expect("Execution failed");
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
        let compiler = build("fn main(x) { (true, x+1) }");
        let result = compiler
            .run_fn_i_tuple::<isize, bool, isize>("main", 42)
            .expect("Execution failed");
        assert_eq!(result, (true, 43));
    }

    #[test]
    fn fn_signature() {
        let compiler = build("fn main(x) { string_len(x) }");
        let signature = compiler.fn_signature("main").unwrap();
        assert_eq!(signature, "(string) → int");
    }
}
