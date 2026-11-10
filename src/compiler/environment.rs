// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Determine a compilation's module environment before inspecting foreign definitions.
//!
//! Imports and qualified source paths establish the roots. Closing them over recorded
//! dependencies uses only module metadata, so stale definitions are never needed to discover
//! that compilation must wait. Selection cannot add roots to this environment.

use crate::{
    FxHashSet, Modules,
    ast::{self, ExprKind, LetPatternKind, PExprArena, PModule, PType, PatternKind, UseTree},
    module::{Module, ModuleId, Path},
    std::STD_MODULE_ID,
    types::{
        r#type::{Type, TypeKind},
        type_like::TypeLike,
        type_scheme::{PubTypeConstraint, TypeScheme},
        type_visitor::TypeInnerVisitor,
    },
};

struct EnvironmentCollector<'a> {
    modules: &'a Modules,
    roots: FxHashSet<ModuleId>,
}

impl EnvironmentCollector<'_> {
    fn module_path(&mut self, path: &Path) {
        if let Some(id) = self.modules.get_id_by_name(path) {
            self.roots.insert(id);
        }
    }

    fn path(&mut self, path: &ast::Path) {
        // One final segment is a symbol; a second may be a trait method or enum variant.
        // Collect both possible module prefixes without inspecting either definition.
        for len in [
            path.segments.len().saturating_sub(1),
            path.segments.len().saturating_sub(2),
        ] {
            if len > 0 {
                self.module_path(&Path::from_ast_segments(&path.segments[..len]));
            }
        }
    }

    fn type_path(&mut self, path: &ast::Path) {
        if let Some((_, module)) = path.segments.split_last()
            && !module.is_empty()
        {
            self.module_path(&Path::from_ast_segments(module));
        }
    }

    fn import(&mut self, tree: &UseTree, prefix: &[ast::UstrSpan]) {
        let (path, children, glob) = match tree {
            UseTree::Glob(path, _) => (path.as_ref(), None, true),
            UseTree::Group(path, children) => (path.as_ref(), Some(children), false),
            UseTree::Name(path) => (Some(path), None, false),
        };
        let mut segments = prefix.to_vec();
        if let Some(path) = path {
            segments.extend_from_slice(&path.segments);
        }
        if let Some(children) = children {
            for child in children {
                self.import(child, &segments);
            }
        } else {
            if !glob {
                segments.pop();
            }
            self.module_path(&Path::from_ast_segments(&segments));
        }
    }

    fn ty(&mut self, ty: &PType) {
        match ty {
            PType::Path(path) => self.type_path(path),
            PType::AppliedPath { path, args, .. } => {
                self.type_path(path);
                for (ty, _) in args {
                    self.ty(ty);
                }
            }
            PType::Variant(fields) | PType::Record(fields) => {
                for (_, (ty, _)) in fields {
                    self.ty(ty);
                }
            }
            PType::Tuple(fields) => {
                for (ty, _) in fields {
                    self.ty(ty);
                }
            }
            PType::Array(ty) => self.ty(&ty.0),
            PType::Function(function) => {
                for arg in &function.args {
                    self.ty(&arg.ty.0);
                }
                self.ty(&function.ret.0);
            }
            PType::Resolved(ty) => self.resolved_type(ty),
            PType::Never | PType::Unit | PType::Infer => {}
        }
    }

    fn resolved_type(&mut self, ty: &impl TypeLike) {
        ty.visit(self);
    }

    fn resolved_constraints(&mut self, constraints: &[PubTypeConstraint]) {
        for constraint in constraints {
            if let PubTypeConstraint::HaveTrait { trait_id, .. } = constraint {
                self.roots.insert(trait_id.module);
            }
            self.resolved_type(constraint);
        }
    }

    fn resolved_scheme(&mut self, scheme: &TypeScheme<impl TypeLike>) {
        self.resolved_type(&scheme.ty);
        self.resolved_constraints(&scheme.constraints);
    }

    fn declarations(&mut self, module: &Module) {
        for alias in module.type_aliases.type_entries() {
            self.resolved_type(&alias.ty);
        }
        for def in module.type_defs.as_slice() {
            self.resolved_scheme(&def.def().shape);
        }
        for function in &module.functions {
            self.resolved_scheme(&function.definition.ty_scheme);
        }
        for tr in module.traits.as_slice() {
            self.resolved_constraints(&tr.parent_constraints);
            self.resolved_constraints(&tr.constraints);
            for (_, method) in &tr.methods {
                self.resolved_scheme(&method.ty_scheme);
            }
            for constant in &tr.associated_consts {
                self.resolved_type(&constant.ty);
            }
        }
        for key in module.impls.concrete().keys() {
            self.roots.insert(key.trait_id.module);
            for ty in &key.input_tys {
                self.resolved_type(ty);
            }
        }
        for (&trait_id, entries) in module.impls.blanket() {
            self.roots.insert(trait_id.module);
            for key in entries.keys() {
                for ty in &key.input_tys {
                    self.resolved_type(ty);
                }
                self.resolved_constraints(&key.constraints);
            }
        }
        for imp in module.impls.data.iter() {
            for ty in &imp.output_tys {
                self.resolved_type(ty);
            }
        }
    }

    fn constraints(&mut self, constraints: &[ast::PTypeConstraint]) {
        for constraint in constraints {
            self.type_path(&constraint.trait_name);
            for input in &constraint.input_types {
                self.ty(&input.ty.0);
            }
            for output in &constraint.output_types {
                self.ty(&output.ty.0);
            }
        }
    }

    fn signature(
        &mut self,
        args: &[ast::PModuleFunctionArg],
        ret: &Option<ast::PTypeSpan>,
        constraints: &[ast::PTypeConstraint],
    ) {
        for arg in args {
            if let Some((_, ty, _)) = &arg.ty {
                self.ty(ty);
            }
        }
        if let Some((ty, _)) = ret {
            self.ty(ty);
        }
        self.constraints(constraints);
    }

    fn module(&mut self, module: &PModule) {
        for tree in &module.uses {
            self.import(tree, &[]);
        }
        for alias in &module.type_aliases {
            self.ty(&alias.ty.0);
        }
        for def in &module.type_defs {
            self.ty(&def.shape);
            self.constraints(&def.where_clause);
        }
        for function in &module.functions {
            self.signature(&function.args, &function.ret_ty, &function.where_clause);
        }
        for subscript in &module.subscripts {
            if let Some((ty, _)) = &subscript.projection_receiver {
                self.ty(ty);
            }
            self.signature(&subscript.args, &subscript.ret_ty, &subscript.where_clause);
        }
        for imp in &module.impls {
            if let Some(header) = &imp.for_trait {
                for input in &header.input_types {
                    self.ty(&input.ty.0);
                }
                for output in &header.output_types {
                    self.ty(&output.ty.0);
                }
            }
            self.constraints(&imp.where_clause);
            for function in &imp.functions {
                self.signature(&function.args, &function.ret_ty, &function.where_clause);
            }
        }
        for tr in &module.traits {
            self.constraints(&tr.parent_constraints);
            self.constraints(&tr.where_clause);
            for constant in &tr.associated_consts {
                self.ty(&constant.ty.0);
            }
            for method in &tr.methods {
                for arg in &method.args {
                    self.ty(&arg.ty.ty.0);
                }
                if let Some((ty, _)) = &method.ret_ty {
                    self.ty(ty);
                }
            }
        }
    }

    fn pattern(&mut self, pattern: &ast::PLetPattern) {
        match &pattern.kind {
            LetPatternKind::Tuple { path, elements, .. } => {
                if let Some(path) = path {
                    self.path(path);
                }
                for element in elements {
                    self.pattern(element);
                }
            }
            LetPatternKind::Record { path, fields, .. } => {
                if let Some(path) = path {
                    self.path(path);
                }
                for field in fields {
                    self.pattern(&field.pattern);
                }
            }
            LetPatternKind::Binding { .. } | LetPatternKind::Ignore => {}
        }
    }

    fn expressions(&mut self, arena: &PExprArena) {
        // The arena includes bodies, default methods and the optional REPL expression.
        for (_, expr) in arena.iter() {
            match &expr.kind {
                ExprKind::Identifier(path) => self.path(path),
                ExprKind::PropertyPath(data) => self.path(&data.path),
                ExprKind::StructLiteral(data) => self.path(&data.path),
                ExprKind::AssignOp(data) => self.path(&data.op_path),
                ExprKind::TypeAscription(data) => self.ty(&data.ty),
                ExprKind::TraitAssociatedConst(data) => {
                    self.type_path(&data.trait_name);
                    for (ty, _) in &data.input_tys {
                        self.ty(ty);
                    }
                }
                ExprKind::Let(data) => self.pattern(&data.pattern),
                ExprKind::ForLoop(data) => self.pattern(&data.pattern),
                ExprKind::Match(data) => {
                    for (pattern, _) in &data.alternatives {
                        if let PatternKind::Variant { path, .. } = &pattern.kind {
                            self.path(&path.path);
                        }
                    }
                }
                ExprKind::Literal(_, ty) => self.resolved_type(ty),
                _ => {}
            }
        }
    }
}

impl TypeInnerVisitor for EnvironmentCollector<'_> {
    fn visit_ty_kind_start(&mut self, ty: &TypeKind) {
        match ty {
            TypeKind::Named(named) => {
                self.roots.insert(named.def.module);
            }
            TypeKind::Native(native) => {
                // Native declarations belong to host modules. Source aliases name an
                // existing type and do not create another owner.
                if let Some((id, _, _)) = self.modules.enumerate().find(|(_, entry, _)| {
                    entry.src_info.is_none()
                        && entry
                            .module()
                            .is_some_and(|module| module.owns_native_type(native))
                }) {
                    self.roots.insert(id);
                }
            }
            _ => {}
        }
    }
}

pub(crate) struct CollectedEnvironment {
    /// Roots are recorded for invalidation even when no impl or value is selected from them.
    pub(crate) roots: FxHashSet<ModuleId>,
    /// The transitive closure determines eligible lookup, not direct dependency edges.
    pub(crate) modules: FxHashSet<ModuleId>,
}

/// Collect without dereferencing foreign definitions. The caller checks freshness before
/// desugaring, inference or coherence. Existing roots cover native additions and scratch locals.
pub(crate) fn collect_environment(
    module: &Module,
    source: Option<&PModule>,
    arena: &PExprArena,
    modules: &Modules,
    extra_types: impl IntoIterator<Item = Type>,
) -> CollectedEnvironment {
    let mut collector = EnvironmentCollector {
        modules,
        roots: module.deps().collect(),
    };
    if module.module_id() != STD_MODULE_ID && modules.get(STD_MODULE_ID).is_some() {
        collector.roots.insert(STD_MODULE_ID);
    }
    for data in module.uses.explicits.values().chain(&module.uses.wildcards) {
        collector.module_path(&data.module);
    }
    collector.declarations(module);
    if let Some(source) = source {
        collector.module(source);
    }
    collector.expressions(arena);
    for ty in extra_types {
        collector.resolved_type(&ty);
    }
    collector.roots.remove(&module.module_id());
    let mut environment = collector.roots.clone();
    let mut pending: Vec<_> = collector.roots.iter().copied().collect();
    while let Some(id) = pending.pop() {
        if id == module.module_id() {
            continue;
        }
        if let Some(entry) = modules.get(id) {
            for &dep in &entry.latest_deps {
                if environment.insert(dep) {
                    pending.push(dep);
                }
            }
        }
    }
    CollectedEnvironment {
        roots: collector.roots,
        modules: environment,
    }
}

impl CollectedEnvironment {
    /// Freshness is a session concern: defer source compilation before calling HIR emission.
    pub(crate) fn unavailable_dependency(&self, modules: &Modules) -> Option<ModuleId> {
        modules.enumerate().find_map(|(id, entry, _)| {
            (self.modules.contains(&id) && (entry.stale || entry.module().is_none())).then_some(id)
        })
    }

    pub(crate) fn install(self, module: &mut Module) {
        let current = module.module_id();
        module
            .deps
            .extend(self.roots.into_iter().filter(|id| *id != current));
        module.environment = self.modules;
    }
}
