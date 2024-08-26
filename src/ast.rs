use cfgrammar::span::Span;
use enum_as_inner::EnumAsInner;
use itertools::Itertools;
use std::fmt::Debug;

use ustr::Ustr;

use crate::{
    containers::B, error::LocatedError, module::FmtWithModuleEnv, mutability::MutVal, r#type::Type,
    value::Value,
};

#[derive(Debug, Clone)]
pub struct ModuleFunction {
    pub name: (Ustr, Span),
    pub args: Vec<(Ustr, Span)>,
    pub args_span: Span,
    pub body: B<Expr>,
    pub span: Span,
}
impl ModuleFunction {
    pub fn new(
        name: (Ustr, Span),
        args: Vec<(Ustr, Span)>,
        args_span: Span,
        body: B<Expr>,
        span: Span,
    ) -> Self {
        Self {
            name,
            args,
            args_span,
            body,
            span,
        }
    }
}

// A module is a collection of functions and types, and is the top-level structure of the AST
#[derive(Debug, Clone, Default)]
pub struct Module {
    pub functions: Vec<ModuleFunction>,
    pub types: Vec<(Ustr, Type)>,
}
impl Module {
    pub fn new_with_function(
        name: (Ustr, Span),
        args: Vec<(Ustr, Span)>,
        args_span: Span,
        body: Expr,
        span: Span,
    ) -> Self {
        Self {
            functions: vec![ModuleFunction::new(
                name,
                args,
                args_span,
                B::new(body),
                span,
            )],
            ..Default::default()
        }
    }

    pub fn extend(&mut self, other: Self) {
        self.functions.extend(other.functions);
        self.types.extend(other.types);
    }

    pub fn errors(&self) -> Vec<LocatedError> {
        let mut errors = vec![];
        for ModuleFunction { body, .. } in self.functions.iter() {
            body.acc_errors_rec(&mut errors);
        }
        errors
    }

    pub fn is_empty(&self) -> bool {
        self.functions.is_empty() && self.types.is_empty()
    }
}

impl FmtWithModuleEnv for Module {
    fn fmt_with_module_env(
        &self,
        f: &mut std::fmt::Formatter,
        env: &crate::module::ModuleEnv<'_>,
    ) -> std::fmt::Result {
        if !self.types.is_empty() {
            writeln!(f, "Types:")?;
            for (name, ty) in self.types.iter() {
                writeln!(f, "  {}: {}", name, ty.format_with(env))?;
            }
        }
        if !self.functions.is_empty() {
            writeln!(f, "Functions:")?;
            for ModuleFunction {
                name, args, body, ..
            } in self.functions.iter()
            {
                writeln!(
                    f,
                    "  fn {}({}):",
                    name.0,
                    args.iter().map(|(name, _)| name.to_string()).join(", ")
                )?;
                body.format_ind(f, 2)?;
            }
        }
        Ok(())
    }
}

// FIXME: think whether it would be better to only use span here
// and pass the source code in the type inference phase.

/// The kind-specific part of an expression as an Abstract Syntax Tree
#[derive(Debug, Clone)]
pub enum ExprKind {
    Literal(Value, Type),
    FormattedString(String),
    /// A variable, or a function from the module environment, or a null-ary variant constructor
    Identifier(Ustr),
    LetVar((Ustr, Span), MutVal, B<Expr>),
    Abstract(Vec<(Ustr, Span)>, B<Expr>),
    Apply(B<Expr>, Vec<Expr>),
    /// A function from the module environment, or a variant constructor
    StaticApply(Ustr, Span, Vec<Expr>),
    Block(Vec<Expr>),
    Assign(B<Expr>, Span, B<Expr>),
    Tuple(Vec<Expr>),
    Project(B<Expr>, usize, Span),
    Record(Vec<(Ustr, Span, Expr)>),
    FieldAccess(B<Expr>, Ustr, Span),
    Array(Vec<Expr>),
    Index(B<Expr>, B<Expr>),
    Match(B<Expr>, Vec<(Pattern, Expr)>, Option<B<Expr>>),
    ForLoop((Ustr, Span), B<Expr>, B<Expr>),
    Error(String),
}

/// An expression as an Abstract Syntax Tree
#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}
impl Expr {
    pub fn new(kind: ExprKind, span: Span) -> Self {
        Self { kind, span }
    }

    pub fn format_ind(&self, f: &mut std::fmt::Formatter, indent: usize) -> std::fmt::Result {
        let indent_str = "  ".repeat(indent);
        use ExprKind::*;
        match &self.kind {
            Literal(value, _) => writeln!(f, "{indent_str}{value}"),
            FormattedString(string) => writeln!(f, "{indent_str}f\"{string}\""),
            Identifier(name) => writeln!(f, "{indent_str}{name} (local)"),
            LetVar((name, _), mutable, expr) => {
                let kw = mutable.var_def_string();
                writeln!(f, "{indent_str}{kw} {name} =")?;
                expr.format_ind(f, indent + 1)
            }
            Abstract(args, body) => {
                write!(f, "{indent_str}|")?;
                for (arg, _) in args {
                    write!(f, "{arg}, ")?;
                }
                writeln!(f, "|")?;
                body.format_ind(f, indent + 1)
            }
            Apply(func, args) => {
                writeln!(f, "{indent_str}eval")?;
                func.format_ind(f, indent + 1)?;
                if args.is_empty() {
                    writeln!(f, "{indent_str}and apply to ()")
                } else {
                    writeln!(f, "{indent_str}and apply to (")?;
                    for arg in args {
                        arg.format_ind(f, indent + 1)?;
                    }
                    writeln!(f, "{indent_str})")
                }
            }
            StaticApply(func, _, args) => {
                writeln!(f, "{indent_str}apply {func} to (")?;
                for arg in args {
                    arg.format_ind(f, indent + 1)?;
                }
                writeln!(f, "{indent_str})")
            }
            Block(exprs) => {
                for expr in exprs.iter() {
                    expr.format_ind(f, indent)?;
                }
                Ok(())
            }
            Assign(place, _, value) => {
                writeln!(f, "{indent_str}assign")?;
                place.format_ind(f, indent + 1)?;
                value.format_ind(f, indent + 1)
            }
            Tuple(args) => {
                writeln!(f, "{indent_str}(")?;
                for arg in args.iter() {
                    arg.format_ind(f, indent + 1)?;
                }
                writeln!(f, "{indent_str})")
            }
            Project(expr, index, _) => {
                expr.format_ind(f, indent)?;
                writeln!(f, "{indent_str}  .{index}")
            }
            Record(fields) => {
                writeln!(f, "{indent_str}{{")?;
                for (name, _, value) in fields.iter() {
                    writeln!(f, "{indent_str}  {name}:")?;
                    value.format_ind(f, indent + 2)?;
                    writeln!(f, "{indent_str}  ,")?;
                }
                writeln!(f, "{indent_str}}}")
            }
            FieldAccess(expr, field, _) => {
                expr.format_ind(f, indent)?;
                writeln!(f, "{indent_str}  .{field}")
            }
            Array(args) => {
                if args.is_empty() {
                    writeln!(f, "{indent_str}[]")
                } else {
                    writeln!(f, "{indent_str}[")?;
                    for arg in args.iter() {
                        arg.format_ind(f, indent + 1)?;
                    }
                    writeln!(f, "{indent_str}]")
                }
            }
            Index(expr, index) => {
                expr.format_ind(f, indent)?;
                writeln!(f, "{indent_str}[")?;
                index.format_ind(f, indent + 1)?;
                writeln!(f, "{indent_str}]")
            }
            Match(expr, cases, default) => {
                writeln!(f, "{indent_str}match")?;
                expr.format_ind(f, indent + 1)?;
                for (value, case) in cases.iter() {
                    writeln!(f, "{indent_str}case")?;
                    value.format_ind(f, indent + 1)?;
                    writeln!(f, "{indent_str}=>")?;
                    case.format_ind(f, indent + 1)?;
                }
                if let Some(default) = default {
                    writeln!(f, "{indent_str}case _ =>")?;
                    default.format_ind(f, indent + 1)?;
                }
                Ok(())
            }
            ForLoop(var_name, iterator, body) => {
                writeln!(f, "{indent_str}for {} in", var_name.0)?;
                iterator.format_ind(f, indent + 1)?;
                writeln!(f, "{indent_str}do")?;
                body.format_ind(f, indent + 1)
            }
            Error(msg) => writeln!(f, "{indent_str}Error: {msg}"),
        }
    }
    pub fn format(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.format_ind(f, 0)
    }

    pub fn errors(&self) -> Vec<LocatedError> {
        let mut errors = vec![];
        self.acc_errors_rec(&mut errors);
        errors
    }
    fn acc_errors_rec(&self, errors: &mut Vec<LocatedError>) {
        fn acc_errors<'a, I>(errors: &mut Vec<LocatedError>, exprs: I)
        where
            I: Iterator<Item = &'a Expr>,
        {
            for expr in exprs {
                expr.acc_errors_rec(errors);
            }
        }
        use ExprKind::*;
        match &self.kind {
            LetVar(_, _, expr) => expr.acc_errors_rec(errors),
            Abstract(_, expr) => expr.acc_errors_rec(errors),
            Apply(expr, args) => {
                expr.acc_errors_rec(errors);
                acc_errors(errors, args.iter());
            }
            StaticApply(_, _, args) => acc_errors(errors, args.iter()),
            Block(exprs) => acc_errors(errors, exprs.iter()),
            Assign(place, _, value) => {
                place.acc_errors_rec(errors);
                value.acc_errors_rec(errors);
            }
            Tuple(args) => acc_errors(errors, args.iter()),
            Project(expr, _, _) => expr.acc_errors_rec(errors),
            Array(args) => acc_errors(errors, args.iter()),
            Index(expr, index) => {
                expr.acc_errors_rec(errors);
                index.acc_errors_rec(errors);
            }
            Match(expr, cases, default) => {
                expr.acc_errors_rec(errors);
                acc_errors(errors, cases.iter().map(|(_, expr)| expr));
                if let Some(default) = default {
                    default.acc_errors_rec(errors);
                }
            }
            ForLoop(_, iterator, body) => {
                iterator.acc_errors_rec(errors);
                body.acc_errors_rec(errors);
            }
            Error(error) => errors.push((error.clone(), self.span)),
            _ => {}
        }
    }
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.format(f)
    }
}
/// The kind-specific part of an expression as an Abstract Syntax Tree
#[derive(Debug, Clone, EnumAsInner)]
pub enum PatternKind {
    Literal(Value, Type),
    Variant {
        tag: Ustr,
        tag_span: Span,
        var: Option<(Ustr, Span)>,
    },
    Error(String),
}
impl PatternKind {
    pub fn r#type(&self) -> PatternType {
        use PatternKind::*;
        match self {
            Literal(_, _) => PatternType::Literal,
            Variant { .. } => PatternType::Variant,
            Error(_) => PatternType::Error,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, EnumAsInner)]
pub enum PatternType {
    Literal,
    Variant,
    Error,
}
impl PatternType {
    pub fn name(&self) -> &'static str {
        use PatternType::*;
        match self {
            Literal => "literal",
            Variant => "variant",
            Error => "error",
        }
    }
}

/// An expression as an Abstract Syntax Tree
#[derive(Debug, Clone)]
pub struct Pattern {
    pub kind: PatternKind,
    pub span: Span,
}

impl Pattern {
    pub fn new(kind: PatternKind, span: Span) -> Self {
        Self { kind, span }
    }

    pub fn format_ind(&self, f: &mut std::fmt::Formatter, indent: usize) -> std::fmt::Result {
        let indent_str = "  ".repeat(indent);
        use PatternKind::*;
        match &self.kind {
            Literal(value, _) => writeln!(f, "{indent_str}{value}"),
            Variant { tag, var, .. } => {
                if let Some(var) = var {
                    writeln!(f, "{indent_str}{} {}", tag, var.0)
                } else {
                    writeln!(f, "{indent_str}{}", tag)
                }
            }
            Error(s) => writeln!(f, "{indent_str}Pattern error: {s}"),
        }
    }
}
