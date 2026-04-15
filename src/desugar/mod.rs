// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use itertools::process_results;
use std::mem;

use crate::{FxHashMap, FxHashSet, Modules};
use ustr::{Ustr, ustr};

use crate::{
    Location,
    ast::{
        self, AbstractData, ApplyData, AssignData, DExpr, DExprArena, DExprId, DLetPattern,
        DModule, DModuleFunction, DModuleFunctionArg, DTraitImpl, ExprId, ExprKind,
        FieldAccessData, ForLoopData, IndexData, LetData, LetPatternKind, LetRecordPatternField,
        MatchData, ModuleFunction, ModuleFunctionArg, PExprArena, PLetPattern as LetPattern,
        PModule, PModuleFunction, PModuleFunctionArg, PTraitImpl, PTypeDef, PTypeSpan, Parsed,
        Pattern, PatternConstraintKind, PatternKind, PatternVar, ProjectData, StructLiteralData,
        TypeAscriptionData, UnnamedArg, UstrSpan,
    },
    containers::b,
    effects::EffType,
    error::{
        DuplicatedFieldContext, DuplicatedVariantContext, GenericParamsOwner,
        InternalCompilationError, InvalidEnumDefaultAttributeKind, InvalidGenericParamsKind,
        InvalidTraitConstraintKind, WhatIsNotAProductType, WhichProductTypeIsNot,
    },
    graph::{find_strongly_connected_components, topological_sort_sccs},
    import_resolver::{ModulesResolver, resolve_imports},
    internal_compilation_error,
    module::{Module, ModuleEnv, ModuleId, TypeDefLookupResult},
    mutability::{MutType, MutVal},
    parser_helpers::syn_static_apply,
    std::{array::array_type, math::int_type},
    r#type::{FnArgType, FnType, NativeType, Type, TypeDefRef, TypeVar},
    type_like::TypeLike,
    type_scheme::{PubTypeConstraint, TypeScheme},
};

/// A node of a function dependency graph
#[derive(Debug)]
pub struct DepGraphNode(pub Vec<usize>);

impl crate::graph::Node for DepGraphNode {
    type Index = usize;
    fn neighbors(&self) -> impl Iterator<Item = Self::Index> {
        self.0.iter().copied()
    }
}

pub type FnSccs = Vec<Vec<usize>>;

type FnMap = FxHashMap<Ustr, usize>;
type FnDeps = FxHashSet<usize>;
type GenericTyParams = FxHashMap<Ustr, TypeVar>;

/// Context used for desugaring and collecting function dependencies
#[derive(Debug)]
struct DesugarCtx<'a> {
    /// All functions in the current module, set empty if we are not in a module
    fn_map: &'a FnMap,
    /// Indices from fn_map's keys that are used in this expression
    fn_deps: FnDeps,
    /// Locals for desugaring and function dependencies collection
    locals: Vec<Ustr>,
    /// Module environment, used for desugaring types
    module_env: &'a ModuleEnv<'a>,
    /// Generic type parameters available in the current function, if any.
    generic_ty_params: &'a GenericTyParams,
    /// Counter for generated local names
    temp_counter: usize,
}

impl<'a> DesugarCtx<'a> {
    fn new(
        fn_map: &'a FnMap,
        module_env: &'a ModuleEnv<'a>,
        generic_ty_params: &'a GenericTyParams,
    ) -> Self {
        Self {
            fn_map,
            fn_deps: FxHashSet::default(),
            locals: Vec::new(),
            module_env,
            generic_ty_params,
            temp_counter: 0,
        }
    }
    fn new_with_locals(
        fn_map: &'a FnMap,
        locals: Vec<Ustr>,
        module_env: &'a ModuleEnv<'a>,
        generic_ty_params: &'a GenericTyParams,
    ) -> Self {
        Self {
            fn_map,
            fn_deps: FxHashSet::default(),
            locals,
            module_env,
            generic_ty_params,
            temp_counter: 0,
        }
    }

    fn fresh_generated_local(&mut self, prefix: &str, span: Location) -> UstrSpan {
        let name = ustr(&format!("@{prefix}{}", self.temp_counter));
        self.temp_counter += 1;
        (name, span)
    }
}

fn new_desugared_arena_sized_from_parsed_arena(parsed_arena: &PExprArena) -> DExprArena {
    // We estimate we need 20% more nodes due to desugaring.
    let estimated_node_cound = parsed_arena.len() * 12 / 10;
    DExprArena::with_capacity(estimated_node_cound)
}

mod expr;
mod format_string;
mod module;
mod patterns;
mod types;

pub use expr::desugar_expr_with_empty_ctx;
