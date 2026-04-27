// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use std::sync::LazyLock;

use crate::{
    CompilationError, CompilerSession, DisplayStyle, EvalExprError, FxHashMap, FxHashSet,
    ModuleAndExpr, ModuleEnv, Path, SourceId, call_fn,
    eval::{ValOrMut, eval_node},
    format::FormatWith,
    hir::hir_syn::local,
    hir::value::{NativeValue, Value},
    run_fn_native,
    types::r#type::{Type, tuple_type},
};
use regex::Regex;
#[cfg(target_arch = "wasm32")]
use wasm_bindgen::prelude::*;

use super::{
    annotations::AnnotationData,
    char_index_lookup::CharIndexLookup,
    diagnostics::{ErrorData, compilation_error_to_data},
    execution::{ExecutionErrorData, ExecutionResult},
    signatures::{FunctionSignature, remove_effects},
};

/// The compiler to be used in the web IDE
#[cfg_attr(target_arch = "wasm32", wasm_bindgen)]
pub struct Compiler {
    session: CompilerSession,
    user_module: ModuleAndExpr,
    char_index_lookup: FxHashMap<SourceId, CharIndexLookup>,
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
            char_index_lookup: FxHashMap::default(),
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
            .expect_compiled_module(self.user_module.module_id);
        if let Some(func) = module
            .lookup_function(name, self.session.modules())
            .ok()
            .flatten()
        {
            let module_env = ModuleEnv::new(module, self.session.modules());
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

    pub fn run_expr(&mut self) -> Option<ExecutionResult> {
        self.user_module.expr.as_ref().map(|expr| {
            let module_id = self.user_module.module_id;
            let is_stale = self.session.modules().get(module_id).unwrap().is_stale();
            if is_stale {
                let module_name = self
                    .session
                    .modules()
                    .get_name(module_id)
                    .map_or("".into(), |path| path.to_string());
                return ExecutionResult::error(ExecutionErrorData::new(
                    "Stale module".into(),
                    format!("Module {module_name} is stale and cannot be executed"),
                    None,
                ));
            }
            let value = {
                let module = self.session.expect_fresh_module(module_id);
                eval_node(
                    &module.ir_arena,
                    expr.expr,
                    module_id,
                    &expr.locals,
                    &self.session,
                )
            };
            match value {
                Ok(value) => {
                    let value = value.into_value();
                    let rendered = match self.session.eval_expr_with_locals(
                        "<ide:to_string>",
                        "to_string(value)",
                        module_id,
                        vec![local("value", expr.ty.ty)],
                        vec![ValOrMut::Val(value.clone())],
                    ) {
                        Ok(rendered) => {
                            let rendered = rendered
                                .into_primitive_ty::<crate::std::string::String>()
                                .expect("to_string(value) must return a Ferlium string");
                            rendered.to_string()
                        }
                        Err(EvalExprError::Compilation(error)) => {
                            let summary = "Formatting error".to_string();
                            let complete =
                                format!("{}", error.format_with(self.session.source_table()));
                            return ExecutionResult::error(ExecutionErrorData::new(
                                summary, complete, None,
                            ));
                        }
                        Err(EvalExprError::Runtime(error)) => {
                            let summary = "Formatting error".to_string();
                            let complete = format!(
                                "{}",
                                error.format_with(&(
                                    self.session.source_table(),
                                    self.session.modules()
                                ))
                            );
                            return ExecutionResult::error(ExecutionErrorData::new(
                                summary, complete, None,
                            ));
                        }
                    };
                    let module = self.session.expect_fresh_module(module_id);
                    let module_env = ModuleEnv::new(module, self.session.modules());
                    let output =
                        format!("{}: {}", rendered, expr.ty.display_rust_style(&module_env));
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
        let user_module = &self
            .session
            .expect_module_entry(self.user_module.module_id)
            .module;
        for (mod_name, entry) in self.session.modules().iter_named() {
            let module = match entry.module() {
                None => continue,
                Some(module) => module,
            };
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
        let user_module = &self
            .session
            .expect_module_entry(self.user_module.module_id)
            .module;
        for (mod_name, entry) in self.session.modules().iter_named() {
            let module = match entry.module() {
                None => continue,
                Some(module) => module,
            };
            for (sym_name, _) in module.iter_named_functions() {
                let module = match entry.module() {
                    None => continue,
                    Some(module) => module,
                };
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

/// The compiler to be used in the web IDE, non-wasm-available part
impl Compiler {
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
