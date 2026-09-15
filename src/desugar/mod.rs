// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use std::mem;

use itertools::process_results;

use crate::graph;

mod import_resolver;

use import_resolver::{ModulesResolver, resolve_imports};
use ustr::{Ustr, ustr};

use crate::{
    FxHashMap, FxHashSet, Location, Modules,
    ast::{
        self, AbstractData, ApplyData, AssignData, DExpr, DExprArena, DExprId, DLetPattern,
        DModule, DModuleFunction, DModuleFunctionArg, DTraitImpl, ExprId, ExprKind,
        FieldAccessData, ForLoopData, IndexData, LetData, LetPatternKind, LetRecordPatternField,
        MatchData, ModuleFunction, ModuleFunctionArg, PExprArena, PFnEffects,
        PLetPattern as LetPattern, PModule, PModuleFunction, PModuleFunctionArg, PTraitImpl,
        PTypeAlias, PTypeDef, Parsed, Path, Pattern, PatternConstraintKind, PatternKind,
        PatternVar, ProjectData, StructLiteralData, TypeAscriptionData, UnnamedArg, UstrSpan,
    },
    compiler::{
        CompilationCapabilities,
        error::{
            DuplicatedFieldContext, DuplicatedVariantContext, GenericParamsOwner, InfiniteTypeKind,
            InternalCompilationError, InvalidEnumDefaultAttributeKind, InvalidGenericParamsKind,
            InvalidTraitConstraintKind, WhatIsNotAProductType, WhichProductTypeIsNot,
        },
    },
    containers::b,
    graph::{find_strongly_connected_components, topological_sort_sccs},
    internal_compilation_error,
    module::{Module, ModuleEnv, ModuleId, TypeDefId, TypeDefLookupResult},
    parser::helpers::syn_static_apply,
    std::{STD_MODULE_ID, math::int_type},
    types::{
        effects::{EffType, Effect, EffectVar, EffectsInstSubst, PrimitiveEffect},
        mutability::{MutType, MutVal},
        r#type::{FnArgType, FnType, NativeType, Type, TypeDef as HirTypeDef, TypeVar},
        type_like::TypeLike,
        type_scheme::{PubTypeConstraint, TypeScheme},
    },
};

/// A node of a function dependency graph
#[derive(Debug)]
pub struct DepGraphNode(pub Vec<usize>);

impl graph::Node for DepGraphNode {
    type Index = usize;
    fn neighbors(&self) -> impl Iterator<Item = Self::Index> {
        self.0.iter().copied()
    }
}

pub type FnSccs = Vec<ast::FunctionScc>;
pub type ModuleImplementationSccs = Vec<ast::ModuleImplementationScc>;

type FnMap = FxHashMap<Ustr, usize>;
type SubscriptMap = FxHashMap<Ustr, Vec<usize>>;
type FnDeps = FxHashSet<usize>;
type GenericTyParams = FxHashMap<Ustr, TypeVar>;
type GenericEffParams = FxHashMap<Ustr, EffectVar>;

fn primitive_effect_by_name(name: Ustr) -> Option<PrimitiveEffect> {
    match name.as_str() {
        "read" => Some(PrimitiveEffect::Read),
        "write" => Some(PrimitiveEffect::Write),
        "fallible" => Some(PrimitiveEffect::Fallible),
        _ => None,
    }
}

fn desugar_fn_effects(
    effects: &PFnEffects,
    generic_eff_params: Option<&GenericEffParams>,
) -> Result<EffType, InternalCompilationError> {
    match effects {
        PFnEffects::ImplicitPure => Ok(EffType::empty()),
        // Always emit variable id 0 here; type inference will freshen it later.
        PFnEffects::ImplicitGeneric => Ok(EffType::single_variable_id(0)),
        PFnEffects::Explicit(effects) => {
            let mut result = EffType::empty();
            for effect in effects {
                let (name, span) = effect.name;
                if let Some(primitive) = primitive_effect_by_name(name) {
                    result.insert(Effect::Primitive(primitive));
                } else if let Some(var) =
                    generic_eff_params.and_then(|params| params.get(&name).copied())
                {
                    result.insert(Effect::Variable(var));
                } else {
                    return Err(internal_compilation_error!(EffectNotFound { name, span }));
                }
            }
            Ok(result)
        }
    }
}

/// Context used for desugaring and collecting function dependencies
#[derive(Debug)]
struct DesugarCtx<'a> {
    /// All functions in the current module, set empty if we are not in a module
    fn_map: &'a FnMap,
    /// All subscript member implementation nodes for each named subscript in the current module.
    subscript_map: &'a SubscriptMap,
    /// Projection subscript member implementation nodes by projected field name.
    projection_subscript_map: &'a SubscriptMap,
    /// Indices from fn_map's keys that are used in this expression
    fn_deps: FnDeps,
    /// Locals for desugaring and function dependencies collection
    locals: Vec<Ustr>,
    /// Module environment, used for desugaring types
    module_env: &'a ModuleEnv<'a>,
    /// Generic type parameters available in the current function, if any.
    generic_ty_params: &'a GenericTyParams,
    /// Generic effect parameters available in the current function, if any.
    generic_eff_params: &'a GenericEffParams,
    /// Counter for generated local names
    temp_counter: usize,
}

impl<'a> DesugarCtx<'a> {
    fn new(
        fn_map: &'a FnMap,
        subscript_map: &'a SubscriptMap,
        projection_subscript_map: &'a SubscriptMap,
        module_env: &'a ModuleEnv<'a>,
        generic_ty_params: &'a GenericTyParams,
        generic_eff_params: &'a GenericEffParams,
    ) -> Self {
        Self {
            fn_map,
            subscript_map,
            projection_subscript_map,
            fn_deps: FxHashSet::default(),
            locals: Vec::new(),
            module_env,
            generic_ty_params,
            generic_eff_params,
            temp_counter: 0,
        }
    }
    fn new_with_locals(
        fn_map: &'a FnMap,
        subscript_map: &'a SubscriptMap,
        projection_subscript_map: &'a SubscriptMap,
        locals: Vec<Ustr>,
        module_env: &'a ModuleEnv<'a>,
        generic_ty_params: &'a GenericTyParams,
        generic_eff_params: &'a GenericEffParams,
    ) -> Self {
        Self {
            fn_map,
            subscript_map,
            projection_subscript_map,
            fn_deps: FxHashSet::default(),
            locals,
            module_env,
            generic_ty_params,
            generic_eff_params,
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
