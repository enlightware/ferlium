// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use std::sync::LazyLock;

#[cfg(all(target_arch = "wasm32", feature = "wasm-text"))]
use crate::wasm::text::module_text;
use crate::{
    CompilationOutput, CompilerSession, DiagnosticSeverity, FxHashMap, FxHashSet, MirOptimization,
    ModuleEnv, Path, SourceId, call_fn,
    emit_mir::MirText,
    eval::RuntimeError,
    execution::{DEFAULT_INTERACTIVE_FUEL_LIMIT, ExecutionTarget, ReferenceInterpreterLimits},
    format::FormatWith,
    hir::value::{NativeValue, Value},
    module::{LocalFunctionId, ModuleId, Uses},
    run_fn_native,
    types::{
        r#type::{Type, tuple_type},
        type_scheme_display::TypeSchemeConstraintRenderMode,
    },
};
#[cfg(target_arch = "wasm32")]
use crate::{
    module::FunctionId,
    wasm::{WasmLimits, run_boxed_entry},
};
use regex::Regex;
#[cfg(target_arch = "wasm32")]
use wasm_bindgen::prelude::*;

use super::{
    annotations::{AnnotationData, display_annotations},
    diagnostics::{CompilationReport, ErrorData, compilation_error_to_data},
    execution::{ExecutionErrorData, ExecutionResult, IrText, TextSourceMapEntry},
    position_index_lookup::{PositionEncoding, PositionIndexLookup},
    signatures::{FunctionSignature, remove_effects},
};

/// Compiler services for IDE integrations.
#[cfg_attr(target_arch = "wasm32", wasm_bindgen)]
pub struct Compiler {
    session: CompilerSession,
    user_module: CompilationOutput,
    uses: Uses,
    position_encoding: PositionEncoding,
    position_index_lookup: FxHashMap<SourceId, PositionIndexLookup>,
    execution_fuel_limit: Option<usize>,
    source_name: String,
    repl_counter: usize,
    repl_module: Option<ModuleId>,
}

const SRC_NAME: &str = "<ide>";
const MODULE_NAME: &str = "ide";

/// IDE operations that are also available through WebAssembly.
#[cfg_attr(target_arch = "wasm32", wasm_bindgen)]
impl Compiler {
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen(constructor))]
    pub fn new() -> Self {
        Self::new_with_session_and_uses(CompilerSession::new(), Uses::new_with_std())
    }

    pub fn set_allow_experimental(&mut self, allow: bool) {
        self.session.set_allow_experimental(allow);
    }

    /// Selects the encoding used for every absolute source and rendered-text position returned by
    /// this compiler. The default is [`PositionEncoding::UnicodeScalar`].
    pub fn set_position_encoding(&mut self, encoding: PositionEncoding) {
        if self.position_encoding != encoding {
            self.position_encoding = encoding;
            self.position_index_lookup.clear();
        }
    }

    pub fn compile(&mut self, src: &str) -> Option<Vec<ErrorData>> {
        let report = self.compile_report(src);
        if report.succeeded {
            None
        } else {
            Some(
                report
                    .diagnostics
                    .into_iter()
                    .filter(|diagnostic| diagnostic.severity == DiagnosticSeverity::Error)
                    .collect(),
            )
        }
    }

    /// Compile source and return every warning or error from this attempt. Warnings do not make
    /// the report unsuccessful and therefore do not disable execution in IDE clients.
    pub fn compile_report(&mut self, src: &str) -> CompilationReport {
        self.compile_report_at(
            src,
            SRC_NAME,
            Path::single_str(MODULE_NAME),
            self.uses.clone(),
        )
    }

    /// Compile a persistent REPL submission, importing earlier definitions with local shadowing.
    pub fn compile_repl_report(&mut self, src: &str) -> CompilationReport {
        let parsed =
            crate::parse_module_and_expr(src, self.session.source_table().next_id(), false);
        let local_symbols = parsed.as_ref().map_or_else(
            |_| FxHashSet::default(),
            |(module, _, _)| module.own_symbols().map(|(sym, _)| sym).collect(),
        );
        let uses = crate::repl::submission_uses(
            &self.session,
            &local_symbols,
            self.repl_counter,
            self.uses.clone(),
        );
        let name = format!("repl{}", self.repl_counter);
        self.repl_counter += 1;
        let report = self.compile_report_at(src, &name, Path::single_str(&name), uses);
        if report.succeeded {
            self.repl_module = Some(self.user_module.module_id);
        }
        report
    }

    fn compile_report_at(
        &mut self,
        src: &str,
        name: &str,
        path: Path,
        uses: Uses,
    ) -> CompilationReport {
        let result = self.session.compile_to(src, name, path.clone(), uses);
        let succeeded = result.is_ok();
        let warning_diagnostics = self
            .session
            .modules()
            .id_by_path(&path)
            .and_then(|module_id| self.session.modules().info(module_id))
            .map(|info| {
                info.diagnostics()
                    .iter()
                    .filter(|diagnostic| diagnostic.severity == DiagnosticSeverity::Warning)
                    .cloned()
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        let mut diagnostics = warning_diagnostics
            .into_iter()
            .map(|diagnostic| {
                ErrorData::from_location_with_severity(
                    diagnostic.location,
                    self.session.source_table(),
                    diagnostic.message,
                    diagnostic.severity,
                )
            })
            .collect::<Vec<_>>();
        match result {
            Ok(output) => {
                self.user_module = output;
                self.source_name = name.to_string();
            }
            Err(error) => diagnostics.extend(compilation_error_to_data(
                &error,
                &self.session.source_table,
            )),
        }
        let diagnostics = diagnostics
            .into_iter()
            .map(|data| self.encode_error_data_positions(data))
            .collect();
        CompilationReport {
            succeeded,
            diagnostics,
        }
    }

    pub fn fn_signature(&self, name: &str) -> Option<String> {
        let module = self
            .session
            .expect_compiled_module(self.user_module.module_id);
        if let Some(func) = module
            .lookup_function(name, self.session.raw_modules())
            .ok()
            .flatten()
        {
            let module_env = ModuleEnv::new(module, self.session.raw_modules());
            let ty_scheme = &func.definition.ty_scheme;
            let ty_var_names =
                ty_scheme.display_ty_var_names_with_source_params(&func.definition.generic_params);
            let type_env = ty_scheme.type_display_env(&module_env, &ty_var_names);
            let mut signature = ty_scheme.ty.format_with(&type_env).to_string();
            if !ty_scheme.constraints.is_empty() {
                signature.push(' ');
                signature.push_str(
                    &ty_scheme
                        .display_constraints_with_type_env(&type_env)
                        .to_string(),
                );
            }
            Some(signature)
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

    pub fn set_execution_fuel_limit(&mut self, fuel_limit: u32) {
        self.execution_fuel_limit = Some(fuel_limit as usize);
    }

    pub fn disable_execution_fuel_limit(&mut self) {
        self.execution_fuel_limit = None;
    }

    pub fn run_expr(&mut self) -> Option<ExecutionResult> {
        self.run_expr_with_target(ExecutionTarget::Hir, MirOptimization::Disabled)
    }

    /// Runs the current expression through the raw or optimized MIR interpreter.
    pub fn run_expr_mir(&mut self, optimized: bool) -> Option<ExecutionResult> {
        self.run_expr_with_target(ExecutionTarget::Mir, MirOptimization::from(optimized))
    }

    /// Physical execution currently reports an explicit backend-unavailable error.
    pub fn run_expr_physical_mir(&mut self) -> Option<ExecutionResult> {
        self.run_expr_with_target(ExecutionTarget::PhysicalMir, MirOptimization::Enabled)
    }

    /// Runs the current expression as generated Wasm, linked into this instance.
    #[cfg(target_arch = "wasm32")]
    pub fn run_expr_wasm(&mut self) -> Option<ExecutionResult> {
        self.run_expr_wasm_optimized(true)
    }

    /// Runs Wasm with the selected MIR optimization setting.
    #[cfg(target_arch = "wasm32")]
    pub fn run_expr_wasm_optimized(&mut self, optimized: bool) -> Option<ExecutionResult> {
        let optimization = MirOptimization::from(optimized);
        self.with_optimization(optimization, true, |compiler| {
            compiler.run_expr_with(optimization, |session, module_id, expr, limits| {
                let limits = WasmLimits {
                    execution: limits.execution,
                    ..WasmLimits::default()
                };
                run_boxed_entry(session, FunctionId::new(module_id, expr), limits)
            })
        })
    }

    /// Returns verified, host-matched physical MIR with source-link metadata.
    pub fn physical_mir_text(&mut self) -> Result<IrText, String> {
        self.physical_mir_text_optimized(true)
    }

    /// Returns physical MIR with the selected MIR optimization setting.
    pub fn physical_mir_text_optimized(&mut self, optimized: bool) -> Result<IrText, String> {
        self.mir_text_at(optimized, true)
    }

    /// Returns the MIR for the current successfully compiled source, with source-link metadata.
    pub fn mir_text(&mut self, optimized: bool) -> IrText {
        self.mir_text_at(optimized, false)
            .expect("semantic MIR preparation is infallible")
    }

    /// Returns the Wasm text of the current successfully compiled module, with source-link
    /// metadata. Every function is compiled; named functions with a scalar signature are exported.
    #[cfg(all(target_arch = "wasm32", feature = "wasm-text"))]
    pub fn wasm_text(&mut self) -> Result<IrText, String> {
        self.wasm_text_optimized(true)
    }

    /// Returns complete module Wasm text with the selected MIR optimization setting.
    #[cfg(all(target_arch = "wasm32", feature = "wasm-text"))]
    pub fn wasm_text_optimized(&mut self, optimized: bool) -> Result<IrText, String> {
        let Some(source_id) = self.compiled_source_id() else {
            return Ok(empty_ir_text());
        };
        self.with_optimization(MirOptimization::from(optimized), true, |compiler| {
            let text = module_text(&compiler.session, compiler.user_module.module_id)
                .map_err(|error| compiler.format_runtime_error(error))?;
            Ok(compiler.ir_text(text, source_id))
        })
    }

    fn mir_text_at(&mut self, optimized: bool, physical: bool) -> Result<IrText, String> {
        let Some(source_id) = self.compiled_source_id() else {
            return Ok(empty_ir_text());
        };
        self.with_optimization(MirOptimization::from(optimized), physical, |compiler| {
            let module_id = compiler.user_module.module_id;
            let text = if physical {
                compiler
                    .session
                    .emit_physical_mir_module_with_source_map(module_id)
                    .map_err(|error| compiler.format_runtime_error(error))?
            } else {
                compiler.session.emit_mir_module_with_source_map(module_id)
            };
            Ok(compiler.ir_text(text, source_id))
        })
    }

    /// The source of the user module, if it is compiled and up to date.
    fn compiled_source_id(&self) -> Option<SourceId> {
        let module_info = self.session.modules().info(self.user_module.module_id)?;
        if module_info.is_stale() || !module_info.has_compiled_module() {
            return None;
        }
        self.session
            .source_table()
            .get_latest_source_by_name(&self.source_name)
            .map(|(source_id, _)| source_id)
    }

    fn format_runtime_error(&self, error: RuntimeError) -> String {
        error
            .format_with(&(self.session.source_table(), self.session.raw_modules()))
            .to_string()
    }

    /// Convert rendered-text byte offsets to editor positions, keeping links to the user source.
    fn ir_text(&mut self, text: MirText, source_id: SourceId) -> IrText {
        let ir_lookup = PositionIndexLookup::new(&text.text, self.position_encoding);
        let source_lookup = self.position_index_lookup(source_id);
        IrText {
            source_map: text
                .source_map
                .into_iter()
                .filter(|entry| entry.span.source_id() == source_id)
                .map(|entry| TextSourceMapEntry {
                    from: u32::try_from(ir_lookup.byte_to_position(entry.from))
                        .expect("playground IR text cannot exceed 4 GiB"),
                    to: u32::try_from(ir_lookup.byte_to_position(entry.to))
                        .expect("playground IR text cannot exceed 4 GiB"),
                    source_from: u32::try_from(
                        source_lookup.byte_to_position(entry.span.start_usize()),
                    )
                    .expect("playground source cannot exceed 4 GiB"),
                    source_to: u32::try_from(
                        source_lookup.byte_to_position(entry.span.end_usize()),
                    )
                    .expect("playground source cannot exceed 4 GiB"),
                    inline_depth: entry.inline_depth,
                })
                .collect(),
            text: text.text,
        }
    }

    fn run_expr_with_target(
        &mut self,
        target: ExecutionTarget,
        optimization: MirOptimization,
    ) -> Option<ExecutionResult> {
        self.run_expr_with(optimization, |session, module_id, expr, limits| {
            session.run_entry_with_limits(target, module_id, expr, vec![], limits)
        })
    }

    /// Runs the current expression with `run`, and renders its value or error.
    fn run_expr_with(
        &mut self,
        optimization: MirOptimization,
        run: impl FnOnce(
            &mut CompilerSession,
            ModuleId,
            LocalFunctionId,
            ReferenceInterpreterLimits,
        ) -> Result<Value, RuntimeError>,
    ) -> Option<ExecutionResult> {
        let expr = self.user_module.expr?;
        Some(self.with_optimization(optimization, false, |compiler| {
            let module_id = compiler.user_module.module_id;
            let is_stale = compiler
                .session
                .modules()
                .info(module_id)
                .unwrap()
                .is_stale();
            if is_stale {
                let module_name = compiler
                    .session
                    .modules()
                    .path(module_id)
                    .map_or("".into(), |path| path.to_string());
                return ExecutionResult::error(ExecutionErrorData::new(
                    "Stale module".into(),
                    format!("Module {module_name} is stale and cannot be executed"),
                    None,
                ));
            }
            let (value, ty) = {
                let module = compiler.session.expect_fresh_module(module_id);
                let function = module.get_function_by_id(expr).unwrap();
                let ty = function.definition.ty_scheme.ty.ret;
                let limits = ReferenceInterpreterLimits::default()
                    .with_fuel_limit(compiler.execution_fuel_limit);
                (run(&mut compiler.session, module_id, expr, limits), ty)
            };
            match value {
                Ok(value) => {
                    let rendered = match compiler.session.value_to_inspect_text_with_fuel(
                        module_id,
                        value,
                        ty,
                        compiler.execution_fuel_limit,
                    ) {
                        Ok(rendered) => rendered,
                        Err(error) => {
                            let summary = "Formatting error".to_string();
                            return ExecutionResult::error(ExecutionErrorData::new(
                                summary, error, None,
                            ));
                        }
                    };
                    let module = compiler.session.expect_fresh_module(module_id);
                    let module_env = ModuleEnv::new(module, compiler.session.raw_modules());
                    let output = format!("{}: {}", rendered, ty.format_with(&module_env));
                    ExecutionResult::success(output)
                }
                Err(error) => {
                    let summary = error.kind().to_string();
                    let complete = format!(
                        "{}",
                        error.format_with(&(
                            compiler.session.source_table(),
                            compiler.session.raw_modules()
                        ))
                    );
                    let source_id = compiler
                        .session
                        .source_table()
                        .get_latest_source_by_name(&compiler.source_name)
                        .unwrap()
                        .0;
                    let data = error.top_most_location_in(source_id).map(|loc| {
                        ErrorData::from_location(
                            loc,
                            compiler.session.source_table(),
                            summary.clone(),
                        )
                    });
                    let data = data.map(|data| compiler.encode_error_data_positions(data));
                    let data = ExecutionErrorData {
                        summary: summary.clone(),
                        complete,
                        data,
                    };
                    ExecutionResult::error(data)
                }
            }
        }))
    }

    pub fn get_annotations(&mut self) -> Vec<AnnotationData> {
        self.get_annotations_with_constraint_mode(TypeSchemeConstraintRenderMode::Full)
    }

    pub fn get_light_annotations(&mut self) -> Vec<AnnotationData> {
        self.get_annotations_with_constraint_mode(TypeSchemeConstraintRenderMode::Light)
    }

    fn get_annotations_with_constraint_mode(
        &mut self,
        constraint_mode: TypeSchemeConstraintRenderMode,
    ) -> Vec<AnnotationData> {
        let (source_id, source_entry) = match self
            .session
            .source_table()
            .get_latest_source_by_name(&self.source_name)
        {
            Some(source) => source,
            None => return Vec::new(),
        };
        let annotations = display_annotations(
            &self.user_module,
            source_id,
            source_entry.source(),
            &self.session,
            constraint_mode,
        );
        let mut annotations = annotations
            .into_iter()
            .map(|(pos, hint)| {
                AnnotationData::new(
                    self.position_index_lookup(source_id).byte_to_position(pos),
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
            .expect_module_entry(self.user_module.module_id)
            .module();
        for (mod_name, module) in self.session.modules().iter_named_modules() {
            for (sym_name, func) in module.iter_named_functions() {
                // skip trait methods
                if !module.is_non_trait_local_function(sym_name) {
                    continue;
                }
                if sym_name.starts_with('@') {
                    continue; // skip hidden functions
                }
                let name = if let Some(module) = user_module
                    && module.uses(mod_name, sym_name)
                {
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
        let mut getters = FxHashSet::default();
        let mut setters = FxHashSet::default();
        let user_module = self
            .session
            .expect_module_entry(self.user_module.module_id)
            .module();
        for (mod_name, module) in self.session.modules().iter_named_modules() {
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
                if let Some(module) = user_module
                    && module.uses(mod_name, sym_name)
                {
                    bin.insert(format!("@{name}"));
                } else {
                    bin.insert(format!("@{mod_name}::{name}"));
                }
            }
        }
        getters.intersection(&setters).cloned().collect()
    }
}

fn empty_ir_text() -> IrText {
    IrText {
        text: String::new(),
        source_map: Vec::new(),
    }
}

/// The compiler to be used in the web IDE, non-wasm-available part
impl Compiler {
    pub fn new_with_session_and_uses(mut session: CompilerSession, uses: Uses) -> Self {
        let user_module = session
            .compile_to("", SRC_NAME, Path::single_str(MODULE_NAME), uses.clone())
            .unwrap();
        Self {
            session,
            user_module,
            uses,
            position_encoding: PositionEncoding::default(),
            position_index_lookup: FxHashMap::default(),
            execution_fuel_limit: Some(DEFAULT_INTERACTIVE_FUEL_LIMIT),
            source_name: SRC_NAME.to_string(),
            repl_counter: 0,
            repl_module: None,
        }
    }

    pub fn repl_has_submission(&self) -> bool {
        self.repl_module.is_some()
    }

    /// REPL module inspection, independent of the terminal frontend.
    pub fn repl_module_text(&self, name: Option<&str>) -> Result<String, String> {
        crate::repl::module_text(&self.session, self.repl_current_module_id(), name)
    }

    pub fn repl_function_text(
        &self,
        function: &str,
        module: Option<&str>,
    ) -> Result<String, String> {
        crate::repl::function_text(
            &self.session,
            self.repl_current_module_id(),
            function,
            module,
        )
    }

    fn repl_current_module_id(&self) -> ModuleId {
        self.repl_module.unwrap_or(self.user_module.module_id)
    }

    /// Inspect a retained submission or named module without changing execution settings.
    pub fn repl_mir_text(
        &mut self,
        name: Option<&str>,
        optimized: bool,
        physical: bool,
    ) -> Result<String, String> {
        if name.is_none() && self.repl_module.is_none() {
            return Err("no successfully compiled submission".to_string());
        }
        let module =
            crate::repl::selected_module(&self.session, self.repl_current_module_id(), name)?;
        self.with_optimization(optimized.into(), physical, |compiler| {
            if physical {
                crate::repl::physical_mir_text(&compiler.session, module)
            } else {
                Ok(compiler.session.emit_mir_module(module))
            }
        })
    }

    pub fn repl_history_text(&self) -> String {
        crate::repl::history_text(&self.session, self.repl_counter)
    }

    /// Select stages for one operation, preserving the caller's session configuration.
    fn with_optimization<T>(
        &mut self,
        optimization: MirOptimization,
        physical: bool,
        operation: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let semantic_before = self.session.mir_optimization();
        let physical_before = self.session.physical_mir_optimization();
        self.session.set_mir_optimization(optimization);
        if physical {
            self.session.set_physical_mir_optimization(optimization);
        }
        let result = operation(self);
        self.session.set_mir_optimization(semantic_before);
        self.session.set_physical_mir_optimization(physical_before);
        result
    }

    fn position_index_lookup(&mut self, source_id: SourceId) -> &mut PositionIndexLookup {
        let encoding = self.position_encoding;
        self.position_index_lookup
            .entry(source_id)
            .or_insert_with(|| {
                PositionIndexLookup::new(
                    self.session
                        .source_table()
                        .get_source_text(source_id)
                        .unwrap(),
                    encoding,
                )
            })
    }

    fn encode_error_data_positions(&mut self, data: ErrorData) -> ErrorData {
        let source_id = data.source_id;
        data.map(|position| {
            u32::try_from(
                self.position_index_lookup(source_id)
                    .byte_to_position(position as usize),
            )
            .expect("playground source cannot exceed 4 GiB")
        })
    }

    pub fn run_fn_unit_unit(&self, name: &str) -> Result<(), String> {
        run_fn_native!(&self.session, self.user_module.module_id, name, [])
    }

    pub fn run_fn_unit_o<O: NativeValue + Clone>(&self, name: &str) -> Result<O, String> {
        run_fn_native!(&self.session, self.user_module.module_id, name, [] -> O)
    }

    pub fn run_fn_unit_tuple<OA: NativeValue + Clone, OB: NativeValue + Clone>(
        &self,
        name: &str,
    ) -> Result<(OA, OB), String> {
        let ret = call_fn!(&self.session, self.user_module.module_id, name, [] -> tuple_type([Type::primitive::<OA>(), Type::primitive::<OB>()]))?;
        let ret_tuple = ret.into_tuple().unwrap();
        let [oa, ob]: [Value; 2] = ret_tuple.into_vec().try_into().unwrap();
        Ok((
            oa.into_primitive_ty::<OA>().unwrap(),
            ob.into_primitive_ty::<OB>().unwrap(),
        ))
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
        let input_val = Value::native(input.clone());
        let ret = call_fn!(&self.session, self.user_module.module_id, name, [input_val => Type::primitive::<I>()] -> tuple_type([Type::primitive::<OA>(), Type::primitive::<OB>()]))?;
        let ret_tuple = ret.into_tuple().unwrap();
        let [oa, ob]: [Value; 2] = ret_tuple.into_vec().try_into().unwrap();
        Ok((
            oa.into_primitive_ty::<OA>().unwrap(),
            ob.into_primitive_ty::<OB>().unwrap(),
        ))
    }

    pub fn run_fn_i_unit<I: NativeValue + Clone>(
        &self,
        name: &str,
        input: I,
    ) -> Result<(), String> {
        run_fn_native!(&self.session, self.user_module.module_id, name, [input => I])
    }

    pub fn run_fn_i_o<I: NativeValue + Clone, O: NativeValue + Clone>(
        &self,
        name: &str,
        input: I,
    ) -> Result<O, String> {
        run_fn_native!(&self.session, self.user_module.module_id, name, [input => I] -> O)
    }
}

impl Default for Compiler {
    fn default() -> Self {
        Compiler::new()
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
    fn repl_submissions_preserve_bindings_and_recover_from_errors() {
        let mut compiler = Compiler::new();
        for source in [
            "pub fn answer() -> int { 1 }",
            "pub fn old() -> int { answer() }",
            "pub fn answer() -> int { 42 }",
            "(answer(), old())",
        ] {
            let report = compiler.compile_repl_report(source);
            assert!(report.succeeded, "{source}: {:?}", report.diagnostics);
        }
        assert_eq!(
            compiler.run_expr().unwrap().text_message(),
            "(42, 1): (int, int)"
        );
        assert!(
            !compiler
                .compile_repl_report("fn broken() -> bool { 1 }")
                .succeeded
        );
        assert_eq!(
            compiler.run_expr().unwrap().text_message(),
            "(42, 1): (int, int)"
        );
        assert!(compiler.compile_repl_report("answer()").succeeded);
        assert_eq!(compiler.run_expr().unwrap().text_message(), "42: int");
    }

    #[test]
    fn repl_inspection_supports_native_command_forms() {
        let mut compiler = Compiler::new();
        assert!(
            compiler
                .repl_module_text(Some("std"))
                .unwrap()
                .contains("string_len")
        );
        assert!(
            compiler
                .compile_repl_report("fn hidden(x: int) -> int { x + 1 }")
                .succeeded
        );
        let function = compiler.repl_function_text("hidden", None).unwrap();
        assert_eq!(
            function,
            compiler.repl_function_text("repl0::hidden", None).unwrap()
        );
        assert_eq!(
            function,
            compiler
                .repl_function_text("hidden", Some("repl0"))
                .unwrap()
        );
        assert_eq!(
            function,
            compiler.repl_function_text("0", Some("repl0")).unwrap()
        );
        assert!(
            compiler
                .repl_module_text(Some("repl0"))
                .unwrap()
                .contains("hidden")
        );
        assert!(compiler.repl_history_text().starts_with("repl0:"));
        assert_eq!(
            compiler.repl_module_text(Some("missing")).unwrap_err(),
            "Module missing not found."
        );
    }

    #[test]
    fn repl_inspection_tracks_submissions_independently_of_ide_source_names() {
        let mut compiler = build("fn ide_function() -> int { 1 }");
        assert!(!compiler.repl_has_submission());
        assert!(
            compiler
                .repl_module_text(None)
                .unwrap()
                .contains("ide_function")
        );
        assert!(
            compiler
                .compile_repl_report("fn repl_function() -> int { 2 }")
                .succeeded
        );
        assert!(compiler.repl_has_submission());
        assert!(
            compiler
                .compile_report("fn replacement() -> int { 3 }")
                .succeeded
        );
        assert!(
            compiler
                .repl_module_text(None)
                .unwrap()
                .contains("repl_function")
        );
        assert!(
            !compiler
                .compile_repl_report("fn broken() -> bool { 1 }")
                .succeeded
        );
        assert!(
            compiler
                .repl_module_text(None)
                .unwrap()
                .contains("repl_function")
        );
    }

    #[test]
    fn repl_mir_inspection_selects_retained_modules() {
        let mut compiler = Compiler::new();
        assert_eq!(
            compiler.repl_mir_text(None, true, false).unwrap_err(),
            "no successfully compiled submission"
        );
        assert_eq!(
            compiler
                .repl_mir_text(Some("missing"), true, false)
                .unwrap_err(),
            "Module missing not found."
        );
        assert!(
            compiler
                .compile_repl_report("pub fn earlier(x: int) -> int { x + 1 }")
                .succeeded
        );
        assert!(
            compiler
                .compile_repl_report("pub fn latest(x: int) -> int { x * 2 }")
                .succeeded
        );
        for physical in [false, true] {
            for optimized in [false, true] {
                let text = compiler
                    .repl_mir_text(Some("repl0"), optimized, physical)
                    .unwrap();
                assert!(text.contains("earlier"));
                assert!(!text.contains("latest"));
                assert!(
                    compiler
                        .repl_mir_text(None, optimized, physical)
                        .unwrap()
                        .contains("latest")
                );
            }
        }
        assert!(compiler.repl_module_text(None).unwrap().contains("latest"));
        assert!(
            !compiler
                .compile_repl_report("fn broken() -> bool { 1 }")
                .succeeded
        );
        assert!(compiler.repl_mir_text(Some("repl2"), true, false).is_err());
        assert!(compiler.repl_mir_text(Some("repl2"), true, true).is_err());
    }

    #[test]
    fn inspection_and_execution_preserve_session_optimization_on_success_and_error() {
        let mut compiler = build("fn next(x: int) -> int { x + 1 } next(1)");
        compiler
            .session
            .set_mir_optimization(MirOptimization::Disabled);
        compiler
            .session
            .set_physical_mir_optimization(MirOptimization::Disabled);
        assert!(!compiler.mir_text(true).text.is_empty());
        assert!(
            !compiler
                .physical_mir_text_optimized(true)
                .unwrap()
                .text
                .is_empty()
        );
        assert_eq!(
            compiler.run_expr_mir(true).unwrap().text_message(),
            "2: int"
        );
        assert_eq!(
            compiler.session.mir_optimization(),
            MirOptimization::Disabled
        );
        assert_eq!(
            compiler.session.physical_mir_optimization(),
            MirOptimization::Disabled
        );
        assert!(compiler.compile_report("loop {}").succeeded);
        compiler.set_execution_fuel_limit(3);
        assert!(
            compiler
                .run_expr_mir(true)
                .unwrap()
                .error_content()
                .is_some()
        );
        assert_eq!(
            compiler.session.mir_optimization(),
            MirOptimization::Disabled
        );
        assert_eq!(
            compiler.session.physical_mir_optimization(),
            MirOptimization::Disabled
        );
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
    fn run_expr_respects_execution_fuel_limit() {
        let mut compiler = build("loop { continue }");
        compiler.set_execution_fuel_limit(2);

        let result = compiler.run_expr().expect("expression should exist");
        let error = result.error_content().expect("execution should fail");

        assert_eq!(error.summary, "Execution fuel exhausted");

        assert!(compiler.compile("40 + 2").is_none());
        compiler.set_execution_fuel_limit(100);
        let recovery = compiler
            .run_expr()
            .expect("replacement expression should exist");
        assert_eq!(recovery.html_message(), "42: int");
    }

    #[test]
    fn mir_execution_modes_and_text_source_maps_are_available() {
        let source = "40 + 2";
        let mut compiler = build(source);

        let raw_result = compiler
            .run_expr_mir(false)
            .expect("expression should exist");
        assert_eq!(raw_result.html_message(), "42: int");
        let raw_mir = compiler.mir_text(false);
        assert!(raw_mir.text.contains("b0:"), "{}", raw_mir.text);
        assert!(raw_mir.source_map.iter().all(|entry| {
            entry.from < entry.to
                && entry.to as usize <= raw_mir.text.len()
                && entry.source_from <= entry.source_to
                && entry.source_to as usize <= source.len()
        }));
        assert!(
            !raw_mir.source_map.is_empty(),
            "source operations should be linked to the MIR text"
        );

        let optimized_result = compiler
            .run_expr_mir(true)
            .expect("expression should exist");
        assert_eq!(optimized_result.html_message(), "42: int");
        let optimized_mir = compiler.mir_text(true);
        assert!(optimized_mir.text.contains("b0:"), "{}", optimized_mir.text);
    }

    #[test]
    fn physical_mir_inspection_and_execution() {
        let source = "fn second(pair: (int, bool)) -> bool { pair.1 } second((42, true))";
        let mut compiler = build(source);
        compiler
            .session
            .set_mir_optimization(MirOptimization::Disabled);
        let physical = compiler.physical_mir_text().unwrap();
        assert!(
            physical.text.contains("address_offset"),
            "{}",
            physical.text
        );
        assert!(!physical.source_map.is_empty());
        assert!(physical.source_map.iter().all(|entry| {
            entry.from < entry.to
                && entry.to as usize <= physical.text.len()
                && entry.source_from <= entry.source_to
                && entry.source_to as usize <= source.len()
        }));
        let result = compiler.run_expr_physical_mir().unwrap();
        assert_eq!(result.html_message(), "true: bool");
        assert_eq!(
            compiler.run_expr_mir(false).unwrap().html_message(),
            "true: bool"
        );

        assert!(
            compiler
                .compile("fn replacement() -> int { 7 } replacement()")
                .is_none()
        );
        let replacement = compiler.physical_mir_text().unwrap();
        assert!(replacement.text.contains("replacement"));
        assert!(!replacement.text.contains("fn second"));
        assert_eq!(
            compiler.run_expr_physical_mir().unwrap().html_message(),
            "7: int"
        );
        assert!(compiler.compile("fn broken() -> bool { 1 }").is_some());
        assert!(compiler.physical_mir_text().unwrap().text.is_empty());
    }

    #[test]
    fn utf16_positions_cover_every_ide_output() {
        let mut compiler = Compiler::new();
        compiler.set_position_encoding(PositionEncoding::Utf16CodeUnit);

        let diagnostic_source = "\"😀\" + 1";
        let report = compiler.compile_report(diagnostic_source);
        let diagnostic = report
            .diagnostics
            .iter()
            .find(|diagnostic| diagnostic.file == SRC_NAME)
            .expect("the invalid addition should have a source diagnostic");
        assert_eq!((diagnostic.from, diagnostic.to), (7, 8));

        let annotation_source = "let a = \"😀\"; let b = 1; b";
        assert!(compiler.compile(annotation_source).is_none());
        let annotation_positions = compiler
            .get_light_annotations()
            .into_iter()
            .map(|annotation| annotation.pos)
            .collect::<Vec<_>>();
        assert_eq!(annotation_positions, [5, 19, 26]);

        let runtime_source = "\"😀\"; [1][9]";
        assert!(compiler.compile(runtime_source).is_none());
        let runtime_error = compiler
            .run_expr()
            .expect("expression should exist")
            .error_data()
            .expect("out-of-bounds access should have a source diagnostic");
        assert_eq!((runtime_error.from, runtime_error.to), (6, 12));

        let mir_source = "\"😀é\"";
        assert!(compiler.compile(mir_source).is_none());
        let mir = compiler.mir_text(false);
        let mir_utf16_len = mir.text.encode_utf16().count();
        let source_utf16_len = mir_source.encode_utf16().count();
        assert!(!mir.source_map.is_empty());
        assert!(mir.source_map.iter().all(|entry| {
            entry.from < entry.to
                && entry.to as usize <= mir_utf16_len
                && entry.source_from <= entry.source_to
                && entry.source_to as usize <= source_utf16_len
        }));
        let physical = compiler.physical_mir_text().unwrap();
        assert!(!physical.source_map.is_empty());
        assert!(physical.source_map.iter().all(|entry| {
            entry.from < entry.to
                && entry.to as usize <= physical.text.encode_utf16().count()
                && entry.source_from <= entry.source_to
                && entry.source_to as usize <= source_utf16_len
        }));
    }

    #[test]
    fn mir_text_is_empty_after_a_failed_compilation() {
        let mut compiler = build("40 + 2");
        assert!(compiler.compile("fn broken() -> bool { 1 }").is_some());

        let mir = compiler.mir_text(false);
        assert!(mir.text.is_empty());
        assert!(mir.source_map.is_empty());
    }

    #[test]
    fn compile_report_keeps_warnings_non_fatal_and_uses_character_offsets() {
        let mut compiler = Compiler::new();
        let source = "fn f() -> int { return 1; é = 2 }";
        let report = compiler.compile_report(source);

        assert!(report.succeeded);
        assert_eq!(report.diagnostics.len(), 2);
        let warning = report
            .diagnostics
            .iter()
            .find(|diagnostic| diagnostic.text == "unreachable code")
            .expect("the unreachable suffix should be reported");
        assert_eq!(warning.severity, DiagnosticSeverity::Warning);
        let warned_text = source.chars().collect::<Vec<_>>()
            [warning.from as usize..warning.to as usize]
            .iter()
            .collect::<String>();
        assert_eq!(warned_text.trim(), "é = 2");

        let execution = compiler
            .run_fn_unit_o::<isize>("f")
            .expect("a warning-only compilation remains executable");
        assert_eq!(execution, 1);
    }

    #[test]
    fn needless_return_diagnostic_does_not_cover_the_following_line() {
        let mut compiler = Compiler::new();
        let source = indoc::indoc! { r#"
            fn factorial(n) {
                if n <= 1 {
                    return 1
                } else {
                    n * factorial(n - 1)
                }
            }

            factorial(5)
        "# };
        let report = compiler.compile_report(source);

        assert!(report.succeeded);
        let warning = report
            .diagnostics
            .iter()
            .find(|diagnostic| diagnostic.text == "needless return")
            .expect("tail return should be reported as needless");
        let warned_text = source.chars().collect::<Vec<_>>()
            [warning.from as usize..warning.to as usize]
            .iter()
            .collect::<String>();
        assert_eq!(warned_text, "return 1");
    }

    #[test]
    fn compile_report_keeps_needless_return_beside_unreachable_code() {
        let mut compiler = Compiler::new();
        let source = indoc::indoc! { r#"
            fn f(x) {
                if x == 0 {
                    return 2;
                };
                return 1;
                let a = 4;
            }
        "# };
        let report = compiler.compile_report(source);

        assert!(report.succeeded);
        let warnings = report
            .diagnostics
            .iter()
            .map(|warning| {
                let warned_text = source.chars().collect::<Vec<_>>()
                    [warning.from as usize..warning.to as usize]
                    .iter()
                    .collect::<String>();
                (warning.text.as_str(), warned_text.trim().to_string())
            })
            .collect::<Vec<_>>();
        assert_eq!(
            warnings,
            [
                ("needless return", "return 1".to_string()),
                ("unreachable code", "let a = 4;".to_string()),
            ]
        );
    }

    #[test]
    fn compile_report_highlights_the_entire_unreachable_suffix() {
        let mut compiler = Compiler::new();
        let source = indoc::indoc! { r#"
            fn f(x) {
                loop {};
                let a = 4;
                return 1;
                let b = 3;
            }
        "# };
        let report = compiler.compile_report(source);

        assert!(report.succeeded);
        assert_eq!(report.diagnostics.len(), 1);
        let warning = &report.diagnostics[0];
        assert_eq!(warning.text, "unreachable code");
        let warned_text = source.chars().collect::<Vec<_>>()
            [warning.from as usize..warning.to as usize]
            .iter()
            .collect::<String>();
        assert_eq!(
            warned_text
                .trim()
                .lines()
                .map(str::trim)
                .collect::<Vec<_>>(),
            ["let a = 4;", "return 1;", "let b = 3;"]
        );
    }

    #[test]
    fn run_expr_array_inspect_respects_execution_fuel_limit() {
        let mut compiler = build(
            r#"
            struct Bad(int)

            impl Inspect for Bad {
                fn inspect(value: Bad) -> string {
                    loop {}
                }
            }

            [Bad(1)]
            "#,
        );
        compiler.set_execution_fuel_limit(8);

        let result = compiler.run_expr().expect("expression should exist");
        let error = result.error_content().expect("formatting should fail");

        assert_eq!(error.summary, "Formatting error");
        assert!(error.complete.contains("Execution fuel exhausted"));
    }

    #[test]
    fn run_expr_inspects_strings_with_quotes() {
        let mut compiler = build(r#""hello""#);

        let result = compiler.run_expr().expect("expression should exist");

        assert_eq!(result.html_message(), r#""hello": string"#);
    }

    #[test]
    fn run_expr_inspects_unit() {
        let mut compiler = build("()");

        let result = compiler.run_expr().expect("expression should exist");

        assert_eq!(result.html_message(), "(): ()");
    }

    #[test]
    fn run_expr_inspect_preserves_named_types() {
        let mut compiler =
            build(r#"struct Person { name: string, age: int } Person { name: "Alice", age: 30 }"#);

        let result = compiler.run_expr().expect("expression should exist");

        assert_eq!(
            result.html_message(),
            r#"Person { age: 30, name: "Alice" }: Person"#
        );
    }

    #[test]
    fn run_expr_renders_functions_opaquely() {
        let mut compiler = build("|| 1");

        let result = compiler.run_expr().expect("expression should exist");

        assert_eq!(result.html_message(), "&lt;function&gt;: () -&gt; int");
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
        let compiler = build("fn main() { (true, (43: int)) }");
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
