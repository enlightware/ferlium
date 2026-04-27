// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use derive_new::new;
use itertools::Itertools;
use std::fmt;

use ustr::Ustr;

use crate::{
    Location,
    compiler::error::LocatedError,
    format::write_with_separator_and_format_fn,
    format::{FormatWith, write_with_separator},
    module::ModuleEnv,
    types::mutability::FormatInFnArg,
    types::type_like::TypeLike,
};

use super::expr::ErrorCollector;
use super::{
    Desugared, ExprArena, ExprId, ExprVisitor, FormatWithIndent, MutTypeTypeSpan, PFnArgType,
    PFnEffects, PTypeConstraint, PTypeSpan, Parsed, Phase, TypeConstraintInput,
    TypeConstraintOutput, TypeSpan, UseTree, UstrSpan, VisitExpr,
};

#[derive(Debug, Clone)]
pub struct ModuleFunctionArg<P: Phase> {
    pub name: UstrSpan,
    pub ty: Option<MutTypeTypeSpan<P>>,
    pub mut_binding: bool,
}

pub type PModuleFunctionArg = ModuleFunctionArg<Parsed>;

pub type DModuleFunctionArg = ModuleFunctionArg<Desugared>;

impl DModuleFunctionArg {
    pub fn locations_and_ty_concreteness(&self) -> (Location, Option<(Location, bool)>) {
        (
            self.name.1,
            self.ty.map(|(mut_ty, ty, span)| {
                let mut_concrete = mut_ty.is_none_or(|m| !m.is_variable());
                let ty_concrete = ty.is_constant();
                (span, mut_concrete && ty_concrete)
            }),
        )
    }
}

#[derive(Debug, Clone, new)]
#[allow(clippy::too_many_arguments)]
pub struct ModuleFunction<P: Phase> {
    pub name: UstrSpan,
    pub generic_params: Vec<UstrSpan>,
    pub args: Vec<ModuleFunctionArg<P>>,
    pub args_span: Location,
    pub ret_ty: Option<TypeSpan<P>>,
    pub where_clause: Vec<P::WhereClause>,
    pub body: ExprId<P>,
    pub span: Location,
    pub doc: Option<String>,
}

/// An AST module function just after parsing
pub type PModuleFunction = ModuleFunction<Parsed>;

/// An AST module function after desugaring
pub type DModuleFunction = ModuleFunction<Desugared>;

#[derive(Debug, Clone)]
pub struct TraitFunctionArg {
    pub name: UstrSpan,
    pub ty: PFnArgType,
}

impl FormatWith<ModuleEnv<'_>> for TraitFunctionArg {
    fn fmt_with(&self, f: &mut fmt::Formatter<'_>, env: &ModuleEnv<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.name.0, self.ty.format_with(env))
    }
}

#[derive(Debug, Clone)]
pub struct TraitFunction {
    pub name: UstrSpan,
    pub args: Vec<TraitFunctionArg>,
    pub ret_ty: Option<PTypeSpan>,
    pub effects: PFnEffects,
    pub span: Location,
    pub doc: Option<String>,
}

#[derive(Debug, Clone)]
pub struct TraitDefinition {
    pub name: UstrSpan,
    pub input_type_names: Vec<UstrSpan>,
    pub output_type_names: Vec<UstrSpan>,
    pub where_clause: Vec<PTypeConstraint>,
    pub functions: Vec<TraitFunction>,
    pub span: Location,
    pub doc: Option<String>,
}

impl TraitDefinition {
    pub(crate) fn iter_input_type_names(&self) -> impl Iterator<Item = Ustr> {
        self.input_type_names.iter().map(|(s, _)| *s)
    }
    pub(crate) fn iter_output_type_names(&self) -> impl Iterator<Item = Ustr> {
        self.output_type_names.iter().map(|(s, _)| *s)
    }
}

pub type PTraitDefinition = TraitDefinition;

/// A trait implementation
#[derive(Debug, Clone)]
pub struct TraitImplFor<P: Phase> {
    pub input_types: Vec<TypeConstraintInput<P>>,
    pub output_types: Vec<TypeConstraintOutput<P>>,
    pub span: Location,
}

impl<P: Phase> FormatWith<ModuleEnv<'_>> for TraitImplFor<P> {
    fn fmt_with(&self, f: &mut fmt::Formatter<'_>, env: &ModuleEnv<'_>) -> fmt::Result {
        if self.output_types.is_empty()
            && self.input_types.len() == 1
            && self.input_types[0].name.is_none()
        {
            return self.input_types[0].ty.0.fmt_with(f, env);
        }

        if self.output_types.is_empty() && self.input_types.iter().all(|input| input.name.is_none())
        {
            write!(f, "<")?;
            write_with_separator_and_format_fn(
                &self.input_types,
                ", ",
                |input_ty, f| input_ty.ty.0.fmt_with(f, env),
                f,
            )?;
            return write!(f, ">");
        }

        write!(f, "<")?;
        for (index, input) in self.input_types.iter().enumerate() {
            if index > 0 {
                write!(f, ", ")?;
            }
            input.fmt_with(f, env)?;
        }
        if !self.output_types.is_empty() {
            write!(f, " |-> ")?;
            write_with_separator_and_format_fn(
                &self.output_types,
                ", ",
                |output_ty, f| output_ty.ty.0.fmt_with(f, env),
                f,
            )?;
        }
        write!(f, ">")
    }
}

impl TraitImplFor<Desugared> {
    pub fn input_tys(&self) -> Vec<<Desugared as Phase>::Type> {
        self.input_types.iter().map(|input| input.ty.0).collect()
    }
    pub fn output_tys(&self) -> Vec<<Desugared as Phase>::Type> {
        self.output_types.iter().map(|output| output.ty.0).collect()
    }
}

/// An AST trait implementation header just after parsing
pub type PTraitImplFor = TraitImplFor<Parsed>;

/// An AST trait implementation header after desugaring
pub type DTraitImplFor = TraitImplFor<Desugared>;

/// A trait implementation
#[derive(Debug, Clone)]
pub struct TraitImpl<P: Phase> {
    pub generic_params: Vec<UstrSpan>,
    pub trait_name: UstrSpan,
    /// Explicit trait inputs and outputs for the implementation header, if any.
    /// When `None`, they are fully inferred from the function signatures.
    pub for_trait: Option<TraitImplFor<P>>,
    pub where_clause: Vec<P::WhereClause>,
    pub functions: Vec<ModuleFunction<P>>,
    pub span: Location,
}

/// An AST trait implementation just after parsing
pub type PTraitImpl = TraitImpl<Parsed>;

/// An AST trait implementation after desugaring
pub type DTraitImpl = TraitImpl<Desugared>;

// A module is a collection of functions and types, and is the top-level structure of the AST
#[derive(Debug, Clone)]
pub struct Module<P: Phase> {
    pub traits: Vec<P::TraitInModule>,
    pub functions: Vec<ModuleFunction<P>>,
    pub impls: Vec<TraitImpl<P>>,
    pub type_aliases: Vec<P::TypeAliasInModule>,
    pub type_defs: Vec<P::TypeDefInModule>,
    pub uses: Vec<UseTree>,
}
impl<P: Phase> Module<P> {
    pub fn single_trait(trait_def: P::TraitInModule) -> Self {
        Self {
            traits: vec![trait_def],
            ..Self::default()
        }
    }
    pub fn single_function(function: ModuleFunction<P>) -> Self {
        Self {
            functions: vec![function],
            ..Self::default()
        }
    }
    pub fn single_impl(imp: TraitImpl<P>) -> Self {
        Self {
            impls: vec![imp],
            ..Self::default()
        }
    }
    pub fn single_type_alias(alias: P::TypeAliasInModule) -> Self {
        Self {
            type_aliases: vec![alias],
            ..Self::default()
        }
    }
    pub fn single_type_def(def: P::TypeDefInModule) -> Self {
        Self {
            type_defs: vec![def],
            ..Self::default()
        }
    }

    pub fn uses_tree(uses: UseTree) -> Self {
        Self {
            uses: vec![uses],
            ..Self::default()
        }
    }

    pub fn extend(&mut self, other: Self) {
        self.traits.extend(other.traits);
        self.functions.extend(other.functions);
        self.impls.extend(other.impls);
        self.type_aliases.extend(other.type_aliases);
        self.type_defs.extend(other.type_defs);
        self.uses.extend(other.uses);
    }

    pub fn merge(mut self, other: Self) -> Self {
        self.extend(other);
        self
    }

    pub fn errors(&self, arena: &ExprArena<P>) -> Vec<LocatedError> {
        self.visit_with(ErrorCollector::default(), arena).0
    }

    pub fn is_empty(&self) -> bool {
        self.traits.is_empty()
            && self.functions.is_empty()
            && self.impls.is_empty()
            && self.type_aliases.is_empty()
            && self.type_defs.is_empty()
            && self.uses.is_empty()
    }
}
impl Module<Parsed> {
    /// Returns all the names defined in this module, including traits, functions, type aliases, and type definitions.
    pub fn own_symbols(&self) -> impl Iterator<Item = UstrSpan> + '_ {
        self.traits
            .iter()
            .map(|trait_def| trait_def.name)
            .chain(self.functions.iter().map(|f| f.name))
            .chain(self.type_aliases.iter().map(|alias| alias.name))
            .chain(self.type_defs.iter().map(|def| def.name))
    }
}

impl<P: Phase> Default for Module<P> {
    fn default() -> Self {
        Self {
            traits: Vec::new(),
            functions: Vec::new(),
            impls: Vec::new(),
            type_aliases: Vec::new(),
            type_defs: Vec::new(),
            uses: Vec::new(),
        }
    }
}

impl<P: Phase> VisitExpr<P> for Module<P> {
    fn visit<V: ExprVisitor<P>>(&self, visitor: &mut V, arena: &ExprArena<P>) {
        for ModuleFunction { body, .. } in self.functions.iter() {
            arena[*body].visit(visitor, arena);
        }
        for imp in self.impls.iter() {
            for ModuleFunction { body, .. } in imp.functions.iter() {
                arena[*body].visit(visitor, arena);
            }
        }
    }
}

/// A wrapper for displaying a module with its expression arena
#[derive(new)]
pub struct ModuleDisplay<'a, P: Phase> {
    pub module: &'a Module<P>,
    pub arena: &'a ExprArena<P>,
}

fn fmt_trait_function(
    f: &mut fmt::Formatter<'_>,
    env: &ModuleEnv<'_>,
    function: &TraitFunction,
    doc_prefix: &str,
) -> fmt::Result {
    if let Some(doc) = &function.doc {
        for line in doc.split("\n") {
            writeln!(f, "{doc_prefix}/// {line}")?;
        }
    }
    write!(f, "{doc_prefix}fn {}(", function.name.0)?;
    write_with_separator_and_format_fn(&function.args, ", ", |arg, f| arg.fmt_with(f, env), f)?;
    write!(f, ")")?;
    if let Some((ret_ty, _)) = &function.ret_ty {
        write!(f, " → {}", ret_ty.format_with(env))?;
    }
    if let PFnEffects::Explicit(effects) = &function.effects {
        write!(f, " !")?;
        if !effects.is_empty() {
            write!(f, " ")?;
            write_with_separator(effects, ", ", f)?;
        }
    }
    writeln!(f, ";")
}

fn fmt_module_function<P: Phase>(
    f: &mut fmt::Formatter<'_>,
    env: &ModuleEnv<'_>,
    arena: &ExprArena<P>,
    function: &ModuleFunction<P>,
    doc_prefix: &str,
    body_indent: usize,
) -> fmt::Result {
    let ModuleFunction {
        name,
        generic_params,
        args,
        ret_ty,
        where_clause,
        body,
        doc,
        ..
    } = function;

    if let Some(doc) = doc {
        for line in doc.split("\n") {
            writeln!(f, "{doc_prefix}/// {line}")?;
        }
    }
    write!(f, "    fn {}", name.0)?;
    if !generic_params.is_empty() {
        write!(
            f,
            "<{}>",
            generic_params.iter().map(|(name, _)| name).join(", ")
        )?;
    }
    write!(f, "(")?;
    for (i, arg) in args.iter().enumerate() {
        if i > 0 {
            write!(f, ", ")?;
        }
        if let Some((mut_ty, ty, _)) = &arg.ty {
            write!(f, "{}: ", arg.name.0)?;
            if let Some(mut_ty) = mut_ty {
                mut_ty.format_in_fn_arg(f)?;
            }
            write!(f, "{}", ty.format_with(env))?;
        } else {
            write!(f, "{}", arg.name.0)?;
        }
    }
    write!(f, ")")?;
    if let Some((ret_ty, _)) = ret_ty {
        write!(f, " → {}", ret_ty.format_with(env))?;
    }
    if !where_clause.is_empty() {
        write!(f, " where ")?;
        write_with_separator_and_format_fn(
            where_clause,
            ", ",
            |constraint, f| constraint.fmt_with(f, env),
            f,
        )?;
    }
    writeln!(f)?;
    arena[*body].format_ind(f, env, arena, body_indent)
}

impl<'a> FormatWith<ModuleEnv<'_>> for ModuleDisplay<'a, Parsed> {
    fn fmt_with(&self, f: &mut std::fmt::Formatter, env: &ModuleEnv) -> std::fmt::Result {
        let module = self.module;
        let arena = self.arena;
        if !module.type_aliases.is_empty() {
            writeln!(f, "Types:")?;
            for alias in module.type_aliases.iter() {
                writeln!(f, "  {}", alias.format_with(env))?;
            }
        }
        if !module.traits.is_empty() {
            writeln!(f, "Traits:")?;
            for trait_def in module.traits.iter() {
                if let Some(doc) = &trait_def.doc {
                    for line in doc.split("\n") {
                        writeln!(f, "  /// {line}")?;
                    }
                }
                write!(f, "  trait {}<", trait_def.name.0)?;
                write_with_separator(trait_def.iter_input_type_names(), ", ", f)?;
                if !trait_def.output_type_names.is_empty() {
                    write!(f, " |-> ")?;
                    write_with_separator(trait_def.iter_output_type_names(), ", ", f)?;
                }
                write!(f, ">")?;
                if !trait_def.where_clause.is_empty() {
                    write!(f, " where ")?;
                    write_with_separator_and_format_fn(
                        &trait_def.where_clause,
                        ", ",
                        |constraint, f| constraint.fmt_with(f, env),
                        f,
                    )?;
                }
                writeln!(f, " {{")?;
                for function in &trait_def.functions {
                    fmt_trait_function(f, env, function, "    ")?;
                }
                writeln!(f, "  }}")?;
            }
        }
        if !module.impls.is_empty() {
            writeln!(f, "Trait implementations:")?;
            for TraitImpl {
                generic_params,
                trait_name,
                for_trait,
                where_clause,
                functions,
                ..
            } in module.impls.iter()
            {
                write!(f, "  impl")?;
                if !generic_params.is_empty() {
                    write!(
                        f,
                        "<{}>",
                        generic_params.iter().map(|(name, _)| name).join(", ")
                    )?;
                }
                write!(f, " {}", trait_name.0)?;
                if let Some(for_trait) = for_trait {
                    write!(f, " for {}", for_trait.format_with(env))?;
                } else {
                    write!(f, " ")?;
                }
                if !where_clause.is_empty() {
                    write!(f, " where ")?;
                    write_with_separator_and_format_fn(
                        where_clause,
                        ", ",
                        |constraint, f| constraint.fmt_with(f, env),
                        f,
                    )?;
                    write!(f, " ")?;
                }
                writeln!(f, "{{")?;
                for function in functions.iter() {
                    fmt_module_function(f, env, arena, function, "    ", 3)?;
                }
                writeln!(f, "  }}")?;
            }
        }
        if !module.functions.is_empty() {
            writeln!(f, "Functions:")?;
            for function in module.functions.iter() {
                fmt_module_function(f, env, arena, function, "  ", 2)?;
            }
        }
        Ok(())
    }
}

/// An AST module just after parsing
pub type PModule = Module<Parsed>;

/// An AST module after desugaring
pub type DModule = Module<Desugared>;
