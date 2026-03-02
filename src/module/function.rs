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
    Location,
    ast::UstrSpan,
    containers::b,
    define_id_type,
    dictionary_passing::DictElaborationCtx,
    error::InternalCompilationError,
    format::FormatWith,
    function::{FunctionDefinition, FunctionRc},
    ir::Node,
    module::{ModuleEnv, ModuleId, TraitKey, format_impl_header_by_key, id::Id},
    mutability::MutType,
    r#type::{FnArgType, Type},
};

use derive_new::new;
use ustr::{Ustr, ustr};

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
                let module_id = slot.module;
                let module_name = env
                    .modules
                    .get_name(module_id)
                    .expect("imported module not found");
                write!(f, "imported function {module_name}::")?;
                let function_name = match &slot.target {
                    ImportFunctionTarget::TraitImplMethod { key, index } => {
                        let name = key.trait_ref().functions[*index as usize].0;
                        let imp = env
                            .modules
                            .get(module_id)
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
    /// ID of the module to import from
    pub module: ModuleId,
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

/// Local variable declaration within a function
#[derive(Debug, Clone, new)]
pub struct LocalDecl {
    pub name: UstrSpan,
    pub mut_ty: MutType,
    pub ty: Type,
    /// Span of the type ascription (only for let), if any, and whether it is complete (i.e. not an inferred type)
    pub ty_span: Option<(Location, bool)>,
    pub scope: Location,
}
impl LocalDecl {
    pub fn as_fn_arg_type(&self) -> FnArgType {
        FnArgType::new(self.ty, self.mut_ty)
    }
}

define_id_type!(
    /// Local variable ID within a function
    LocalDeclId
);

/// A local function inside a module.
#[derive(Debug, Clone, new)]
pub struct ModuleFunction {
    pub definition: FunctionDefinition,
    pub code: FunctionRc,
    pub spans: Option<ModuleFunctionSpans>,
    /// Local variable declarations for the function body, including arguments and any variables declared within the function.
    pub locals: Vec<LocalDecl>,
}
impl ModuleFunction {
    pub fn new_without_spans_nor_locals(definition: FunctionDefinition, code: FunctionRc) -> Self {
        Self {
            definition,
            code,
            spans: None,
            locals: Vec::new(),
        }
    }

    pub fn locals_ids(&self) -> Vec<LocalDeclId> {
        (0..self.locals.len())
            .map(LocalDeclId::from_index)
            .collect()
    }

    pub fn get_node(&self) -> Option<Ref<'_, Node>> {
        let code = self.code.borrow();
        Ref::filter_map(code, |code| code.as_script().map(|s| &s.code)).ok()
    }

    pub fn get_node_mut(&mut self) -> Option<RefMut<'_, Node>> {
        let code = self.code.borrow_mut();
        RefMut::filter_map(code, |code| code.as_script_mut().map(|s| &mut s.code)).ok()
    }

    /// Span of the function definition, or synthesized if not available.
    pub fn function_span(&self) -> Location {
        self.spans
            .as_ref()
            .map_or_else(Location::new_synthesized, |s| s.span)
    }

    /// Generate, from the definition and the spans, the local variable declarations for the function arguments.
    pub fn gen_locals_no_bounds(&self) -> Vec<LocalDecl> {
        let (arg_locations, scope): (Box<dyn Iterator<Item = Location>>, Location) =
            if let Some(spans) = &self.spans {
                (b(spans.args.iter().map(|&(span, _)| span)), spans.span)
            } else {
                (
                    b(self
                        .definition
                        .arg_names
                        .iter()
                        .map(|_| Location::new_synthesized())),
                    Location::new_synthesized(),
                )
            };
        self.definition.gen_locals_no_bounds(arg_locations, scope)
    }

    pub fn check_borrows_and_elaborate_dictionaries(
        &mut self,
        ctx: &mut DictElaborationCtx<'_, '_, '_>,
    ) -> Result<(), InternalCompilationError> {
        let mut function = self.code.borrow_mut();
        let script_fn = function.as_script_mut().unwrap();
        let node = &mut script_fn.code;
        node.check_borrows()?;
        // Extend the argument list and the local variable declarations with the dictionaries
        // for the requirements, which are passed as extra arguments to the function.
        // The dictionaries are added at the beginning of the argument list, before the user-defined arguments.
        script_fn.arg_names.splice(
            0..0,
            ctx.dicts
                .requirements
                .iter()
                .enumerate()
                .map(|(i, r)| ustr(&r.to_dict_name(i))),
        );
        let scope = self.function_span();
        let local_count = self.locals.len();
        self.locals
            .extend(ctx.dicts.requirements.iter().enumerate().map(|(i, r)| {
                LocalDecl::new(
                    (ustr(&r.to_dict_name(i)), Location::new_synthesized()),
                    MutType::constant(),
                    r.to_dict_type(),
                    None,
                    scope,
                )
            }));
        node.elaborate_dictionaries(ctx, local_count)
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
        self.code.borrow().format_ind(f, &self.locals, env, 0, 1)
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
