// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

//! Functions within a module

use std::cell::{Ref, RefMut};

use crate::{
    Location, define_id_type,
    format::FormatWith,
    function::{FunctionDefinition, FunctionRc},
    ir::Node,
    module::{ModuleEnv, TraitKey, format_impl_header_by_key, path::Path},
};

use ustr::Ustr;

define_id_type!(
    /// Local function ID within a module
    LocalFunctionId
);

define_id_type!(
    /// Import slot ID for cross-module function references
    ImportFunctionSlotId
);

/// An identifier for a function
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FunctionId {
    /// Local function in a module
    Local(LocalFunctionId),
    /// Imported function through an import slot
    Import(ImportFunctionSlotId),
}

impl FormatWith<ModuleEnv<'_>> for FunctionId {
    fn fmt_with(&self, f: &mut std::fmt::Formatter, env: &ModuleEnv<'_>) -> std::fmt::Result {
        match *self {
            FunctionId::Local(id) => {
                let name = env.current.get_function_name_by_id(id).unwrap();
                write!(f, "local function {name} (#{id})")
            }
            FunctionId::Import(id) => {
                let slot = &env.current.get_import_fn_slot(id).unwrap();
                let module_name = &slot.module;
                write!(f, "imported function {module_name}::")?;
                let function_name = match &slot.target {
                    ImportFunctionTarget::TraitImplMethod { key, index } => {
                        let name = key.trait_ref().functions[*index as usize].0;
                        let imp = env
                            .others
                            .get_value_by_name(module_name)
                            .expect("imported module not found")
                            .get_impl_data_by_trait_key(key)
                            .expect("imported trait impl not found");
                        write!(f, "<")?;
                        format_impl_header_by_key(f, key, imp, env)?;
                        write!(f, ">::")?;
                        name
                    }
                    ImportFunctionTarget::NamedFunction(name) => *name,
                };
                write!(f, "{function_name} (slot #{id})")
            }
        }
    }
}

/// Target of a function import slot
#[derive(Debug, Clone)]
pub enum ImportFunctionTarget {
    /// Name of the function in the target module
    NamedFunction(Ustr),
    /// Trait method to import
    TraitImplMethod {
        /// The concrete trait implementation key
        key: TraitKey,
        /// Index of the method in the trait
        index: u32,
    },
}

/// Import slot that can be resolved to a function from another module
#[derive(Debug, Clone)]
pub struct ImportFunctionSlot {
    /// Name of the module to import from
    pub module: Path,
    /// The target function in that module
    pub target: ImportFunctionTarget,
}

/// A module function argument span, with the span of the optional type ascription.
pub type ModuleFunctionArgSpan = (Location, Option<(Location, bool)>);

/// If the module function is from code, this struct contains the spans of the function.
#[derive(Debug, Clone)]
pub struct ModuleFunctionSpans {
    pub name: Location,
    pub args: Vec<ModuleFunctionArgSpan>,
    pub args_span: Location,
    pub ret_ty: Option<(Location, bool)>,
    pub span: Location,
}

/// A local function inside a module.
#[derive(Debug, Clone)]
pub struct ModuleFunction {
    pub definition: FunctionDefinition,
    pub code: FunctionRc,
    pub spans: Option<ModuleFunctionSpans>,
}
impl ModuleFunction {
    pub fn new_without_spans(definition: FunctionDefinition, code: FunctionRc) -> Self {
        Self {
            definition,
            code,
            spans: None,
        }
    }
    pub fn get_node(&self) -> Option<Ref<'_, Node>> {
        let code = self.code.borrow();
        Ref::filter_map(code, |code| code.as_script().map(|s| &s.code)).ok()
    }
    pub fn get_node_mut(&mut self) -> Option<RefMut<'_, Node>> {
        let code = self.code.borrow_mut();
        RefMut::filter_map(code, |code| code.as_script_mut().map(|s| &mut s.code)).ok()
    }

    pub(crate) fn fmt_code(
        &self,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv<'_>,
    ) -> std::fmt::Result {
        let requirements = self.definition.ty_scheme.extra_parameters().requirements;
        let requirement_count = requirements.len();
        if requirement_count > 0 {
            writeln!(
                f,
                "⎸ {requirement_count} extra argument{} for dictionaries: {}",
                if requirement_count == 1 { "" } else { "s" },
                requirements.format_with(env)
            )?;
        }
        self.code.borrow().format_ind(f, env, 0, 1)
    }
}

impl FormatWith<ModuleEnv<'_>> for (&ModuleFunction, Ustr) {
    fn fmt_with(&self, f: &mut std::fmt::Formatter, env: &ModuleEnv<'_>) -> std::fmt::Result {
        self.0
            .definition
            .fmt_with_name_and_module_env(f, self.1, "", env)?;
        writeln!(f)?;
        self.0.fmt_code(f, env)
    }
}
