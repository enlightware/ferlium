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
use itertools::Itertools;
use std::fmt::{self, Display};

use ustr::Ustr;

use crate::{
    FxHashMap, FxHashSet, Location,
    compiler::error::InternalCompilationError,
    containers::{B, b},
    format::{FormatWith, write_with_separator},
    internal_compilation_error,
    module::ModuleEnv,
    types::effects::PrimitiveEffect,
    types::mutability::FormatInFnArg,
    types::r#type::Type as IrType,
};

use super::{Parsed, Path, Phase, UstrSpan};

pub type TypeSpan<P> = (<P as Phase>::Type, Location);

/// A spanned type alias during parsing
#[derive(Debug, Clone, new)]
pub struct TypeAlias {
    pub name: UstrSpan,
    pub generic_params: Vec<UstrSpan>,
    pub ty: TypeSpan<Parsed>,
}
impl FormatWith<ModuleEnv<'_>> for TypeAlias {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &ModuleEnv) -> std::fmt::Result {
        write!(f, "{}", self.name.0)?;
        if !self.generic_params.is_empty() {
            write!(f, "<")?;
            write_with_separator(self.generic_params.iter().map(|(s, _)| s), ", ", f)?;
            write!(f, ">")?;
        }
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

/// Effect information attached to a parsed function type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PFnEffects {
    ImplicitPure,
    ImplicitGeneric,
    Explicit(Vec<PrimitiveEffect>),
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
            write!(f, " !")?;
            if !effects.is_empty() {
                write!(f, " ")?;
                write_with_separator(effects, ", ", f)?;
            }
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
        PType::AppliedPath { path, args }
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
                    if ty_name == name {
                        return Err(internal_compilation_error!(Unsupported {
                            reason: format!(
                                "Self-referential type paths are not supported, but `{ty_name}` refers to itself"
                            ),
                            span: path.segments[0].1,
                        }));
                    }
                    if let Some(index) = ty_names.get(&ty_name) {
                        collected.insert(*index);
                    }
                }
            }
            AppliedPath { path, args } => {
                if path.segments.len() == 1 {
                    let ty_name = path.segments[0].0;
                    if ty_name == name {
                        return Err(internal_compilation_error!(Unsupported {
                            reason: format!(
                                "Self-referential type paths are not supported, but `{ty_name}` refers to itself"
                            ),
                            span: path.segments[0].1,
                        }));
                    }
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
            Path(path) => write!(f, "{}", path.segments.iter().map(|(s, _)| s).join("::")),
            AppliedPath { path, args } => {
                write!(f, "{path}<")?;
                for (i, (ty, _)) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    ty.fmt_with(f, env)?;
                }
                write!(f, ">")
            }
            Variant(types) => {
                for (i, ((name, _), (ty, _))) in types.iter().enumerate() {
                    if i > 0 {
                        write!(f, " | ")?;
                    }
                    if *ty == Unit {
                        write!(f, "{name}")?;
                    } else {
                        write!(f, "{name} ")?;
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
                    write!(f, "{name}: ")?;
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
