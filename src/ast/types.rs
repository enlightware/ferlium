// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use derive_new::new;
use enum_as_inner::EnumAsInner;
use std::fmt::{self, Display};

use ustr::Ustr;

use crate::{
    FxHashMap, FxHashSet, Location,
    compiler::error::InternalCompilationError,
    containers::{B, b},
    format::{FormatWith, write_identifier, write_identifier_list, write_with_separator},
    module::{ModuleEnv, Visibility},
    types::mutability::FormatInFnArg,
    types::r#type::Type as IrType,
};

use super::{Parsed, Path, Phase, UstrSpan, format_effect_binding_value};

pub type TypeSpan<P> = (<P as Phase>::Type, Location);

/// Generic parameters as written in source.
///
/// The type section preserves the historical `<T, U>` behavior. The optional
/// effect section is written after `!`, for example `<T ! E>`.
#[derive(Debug, Clone, Default, PartialEq, Eq, new)]
pub struct GenericParams {
    type_params: Vec<UstrSpan>,
    effect_params: Vec<UstrSpan>,
}

impl GenericParams {
    pub fn is_empty(&self) -> bool {
        self.type_params.is_empty() && self.effect_params.is_empty()
    }

    pub fn type_params(&self) -> &[UstrSpan] {
        &self.type_params
    }

    pub fn effect_params(&self) -> &[UstrSpan] {
        &self.effect_params
    }

    pub fn format_source(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_empty() {
            return Ok(());
        }
        write!(f, "<")?;
        if !self.type_params.is_empty() {
            write_identifier_list(self.type_params.iter().map(|(s, _)| s.as_str()), ", ", f)?;
        }
        if !self.effect_params.is_empty() {
            if !self.type_params.is_empty() {
                write!(f, " ")?;
            }
            write!(f, "! ")?;
            write_identifier_list(self.effect_params.iter().map(|(s, _)| s.as_str()), ", ", f)?;
        }
        write!(f, ">")
    }
}

/// A spanned type alias during parsing
#[derive(Debug, Clone, new)]
pub struct TypeAlias {
    pub visibility: Visibility,
    pub name: UstrSpan,
    pub generic_params: GenericParams,
    pub ty: TypeSpan<Parsed>,
    pub doc: Option<String>,
}

pub type PTypeAlias = TypeAlias;

impl FormatWith<ModuleEnv<'_>> for TypeAlias {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &ModuleEnv) -> std::fmt::Result {
        write_identifier(f, self.name.0.as_str())?;
        self.generic_params.format_source(f)?;
        write!(f, ": ")?;
        self.ty.0.fmt_with(f, env)
    }
}

/// A spanned Type during parsing
pub type PTypeSpan = TypeSpan<Parsed>;

/// A spanned (MutType, Type)
pub type MutTypeTypeSpan<P> = (Option<<P as Phase>::MutType>, <P as Phase>::Type, Location);

/// A spanned (MutType, Type) during parsing
pub type PMutTypeTypeSpan = MutTypeTypeSpan<Parsed>;
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PMutType {
    Mut,
    Infer,
}
impl Display for PMutType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PMutType::Mut => write!(f, "mut"),
            PMutType::Infer => write!(f, "?"),
        }
    }
}
impl FormatInFnArg for PMutType {
    fn format_in_fn_arg(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "&{self} ")
    }
}

#[derive(Debug, Clone, PartialEq, Eq, new)]
pub struct PFnArgType {
    pub ty: TypeSpan<Parsed>,
    // TODO: currently we do not support generic mutability in type annotations
    pub mut_ty: Option<PMutType>,
    pub span: Location,
}

impl FormatWith<ModuleEnv<'_>> for PFnArgType {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &ModuleEnv<'_>) -> fmt::Result {
        if let Some(mut_ty) = &self.mut_ty {
            write!(f, "&{mut_ty} ")?;
        }
        self.ty.0.fmt_with(f, env)
    }
}

/// A parsed effect name, either a primitive effect or a trait output effect
/// resolved later by desugaring.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PEffect {
    pub name: UstrSpan,
}

impl Display for PEffect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_identifier(f, self.name.0.as_str())
    }
}

/// Effect information attached to a parsed function type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PFnEffects {
    ImplicitPure,
    ImplicitGeneric,
    Explicit(Vec<PEffect>),
}

impl PFnEffects {
    pub fn implicit(has_generic_effects: bool) -> Self {
        if has_generic_effects {
            Self::ImplicitGeneric
        } else {
            Self::ImplicitPure
        }
    }
}

/// The type of a function
#[derive(Debug, Clone, PartialEq, Eq, new)]
pub struct PFnType {
    pub args: Vec<PFnArgType>,
    pub ret: TypeSpan<Parsed>,
    pub effects: PFnEffects,
}
impl PFnType {
    /// Collect indices of types in ty_names that are referenced in this type.
    pub fn collect_refs(
        &self,
        name: Ustr,
        ty_names: &FxHashMap<Ustr, usize>,
        collected: &mut FxHashSet<usize>,
    ) -> Result<(), InternalCompilationError> {
        for arg in &self.args {
            arg.ty.0.collect_refs(name, ty_names, collected)?;
        }
        self.ret.0.collect_refs(name, ty_names, collected)
    }
}

impl FormatWith<ModuleEnv<'_>> for PFnType {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &ModuleEnv<'_>) -> fmt::Result {
        write!(f, "(")?;
        for (i, arg) in self.args.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            arg.fmt_with(f, env)?;
        }
        write!(f, ") -> ")?;
        self.ret.0.fmt_with(f, env)?;
        if let PFnEffects::Explicit(effects) = &self.effects {
            write!(f, " ! ")?;
            format_effect_binding_value(effects, f)?;
        }
        Ok(())
    }
}

/// AST-level type representation before resolution
#[derive(Debug, Clone, PartialEq, Eq, EnumAsInner)]
pub enum PType {
    /// A never type, i.e., a type that cannot have any values
    Never,
    /// A unit type, i.e., `()`
    Unit,
    /// A known, resolved type
    Resolved(IrType),
    /// A type that must be inferred (`_`)
    Infer,
    /// A path to a type
    Path(Path),
    /// A path applied to explicit type arguments
    AppliedPath {
        path: Path,
        args: Vec<TypeSpan<Parsed>>,
        effect_args: Vec<PEffect>,
    },
    /// Tagged union sum type
    Variant(Vec<(UstrSpan, TypeSpan<Parsed>)>),
    /// Position-based product type
    Tuple(Vec<TypeSpan<Parsed>>),
    /// Named product type
    Record(Vec<(UstrSpan, TypeSpan<Parsed>)>),
    /// An array type
    Array(Box<TypeSpan<Parsed>>),
    /// Function type (args -> return)
    Function(B<PFnType>),
}
impl PType {
    pub fn function_type(fn_type: PFnType) -> Self {
        PType::Function(b(fn_type))
    }

    pub fn path_with_args(path: Path, args: Vec<TypeSpan<Parsed>>) -> Self {
        PType::AppliedPath {
            path,
            args,
            effect_args: vec![],
        }
    }

    pub fn path_with_type_and_effect_args(
        path: Path,
        args: Vec<TypeSpan<Parsed>>,
        effect_args: Vec<PEffect>,
    ) -> Self {
        PType::AppliedPath {
            path,
            args,
            effect_args,
        }
    }

    /// Collect indices of types in ty_names that are referenced in this type.
    pub fn collect_refs(
        &self,
        name: Ustr,
        ty_names: &FxHashMap<Ustr, usize>,
        collected: &mut FxHashSet<usize>,
    ) -> Result<(), InternalCompilationError> {
        use PType::*;
        match self {
            #[allow(clippy::collapsible_match)]
            Path(path) => {
                if path.segments.len() == 1 {
                    let ty_name = path.segments[0].0;
                    if let Some(index) = ty_names.get(&ty_name) {
                        collected.insert(*index);
                    }
                }
            }
            AppliedPath { path, args, .. } => {
                if path.segments.len() == 1 {
                    let ty_name = path.segments[0].0;
                    if let Some(index) = ty_names.get(&ty_name) {
                        collected.insert(*index);
                    }
                }
                args.iter()
                    .try_for_each(|(ty, _)| ty.collect_refs(name, ty_names, collected))?;
            }
            Variant(types) => types
                .iter()
                .try_for_each(|(_, (ty, _))| ty.collect_refs(name, ty_names, collected))?,
            Tuple(elements) => elements
                .iter()
                .try_for_each(|(ty, _)| ty.collect_refs(name, ty_names, collected))?,
            Record(fields) => fields
                .iter()
                .try_for_each(|(_, (ty, _))| ty.collect_refs(name, ty_names, collected))?,
            Array(inner) => inner.0.collect_refs(name, ty_names, collected)?,
            Function(fn_type) => fn_type.collect_refs(name, ty_names, collected)?,
            _ => (),
        }
        Ok(())
    }
}

impl FormatWith<ModuleEnv<'_>> for PType {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &ModuleEnv<'_>) -> fmt::Result {
        use PType::*;
        match self {
            Never => write!(f, "never"),
            Unit => write!(f, "()"),
            Resolved(ty) => ty.fmt_with(f, env),
            Infer => write!(f, "_"),
            Path(path) => write!(f, "{path}"),
            AppliedPath {
                path,
                args,
                effect_args,
            } => {
                write!(f, "{path}<")?;
                for (i, (ty, _)) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    ty.fmt_with(f, env)?;
                }
                if !effect_args.is_empty() {
                    if !args.is_empty() {
                        write!(f, " ")?;
                    }
                    write!(f, "! ")?;
                    write_with_separator(effect_args, ", ", f)?;
                }
                write!(f, ">")
            }
            Variant(types) => {
                for (i, ((name, _), (ty, _))) in types.iter().enumerate() {
                    if i > 0 {
                        write!(f, " | ")?;
                    }
                    if *ty == Unit {
                        write_identifier(f, name.as_str())?;
                    } else {
                        write_identifier(f, name.as_str())?;
                        write!(f, " ")?;
                        ty.fmt_with(f, env)?;
                    }
                }
                Ok(())
            }
            Tuple(elements) => {
                write!(f, "(")?;
                for (i, (ty, _)) in elements.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    ty.fmt_with(f, env)?;
                    if elements.len() == 1 {
                        write!(f, ",")?;
                    }
                }
                write!(f, ")")
            }
            Record(fields) => {
                write!(f, "{{ ")?;
                for (i, ((name, _), (ty, _))) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write_identifier(f, name.as_str())?;
                    write!(f, ": ")?;
                    ty.fmt_with(f, env)?;
                }
                write!(f, " }}")
            }
            Array(inner) => {
                write!(f, "[")?;
                inner.0.fmt_with(f, env)?;
                write!(f, "]")
            }
            Function(fn_type) => fn_type.fmt_with(f, env),
        }
    }
}
