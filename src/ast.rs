use cfgrammar::span::Span;
use itertools::Itertools;
use std::fmt::Debug;

use ustr::Ustr;

use crate::{containers::B, error::LocatedError, r#type::Type, value::Value};

// A module is a collection of functions and types, and is the top-level structure of the AST
#[derive(Debug, Clone, Default)]
pub struct Module {
    pub functions: Vec<(Ustr, Vec<Ustr>, B<Expr>)>,
    pub types: Vec<(Ustr, Type)>,
}
impl Module {
    pub fn new_with_function(name: Ustr, args: Vec<Ustr>, body: Expr) -> Self {
        Self {
            functions: vec![(name, args, B::new(body))],
            ..Default::default()
        }
    }

    pub fn extend(&mut self, other: Self) {
        self.functions.extend(other.functions);
        self.types.extend(other.types);
    }

    pub fn errors(&self) -> Vec<LocatedError> {
        let mut errors = vec![];
        for (_, _, body) in self.functions.iter() {
            body.acc_errors_rec(&mut errors);
        }
        errors
    }

    pub fn is_empty(&self) -> bool {
        self.functions.is_empty() && self.types.is_empty()
    }
}

impl std::fmt::Display for Module {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !self.types.is_empty() {
            writeln!(f, "Types:")?;
            for (name, ty) in self.types.iter() {
                writeln!(f, "  {}: {}", name, ty)?;
            }
        }
        if !self.functions.is_empty() {
            writeln!(f, "Functions:")?;
            for (name, args, body) in self.functions.iter() {
                writeln!(
                    f,
                    "  fn {}({}):",
                    name,
                    args.iter().map(ToString::to_string).join(", ")
                )?;
                body.format_ind(f, 2)?;
            }
        }
        Ok(())
    }
}

pub type NodeId = u32;

/// An kind-specific part of an expression as an Abstract Syntax Tree
#[derive(Debug, Clone)]
pub enum ExprKind {
    Literal(Value),
    Variable(Ustr),
    LetVar(Ustr, bool, B<Expr>),
    Abstract(Vec<Ustr>, B<Expr>),
    Apply(B<Expr>, Vec<Expr>),
    StaticApply(Ustr, Vec<Expr>),
    Block(Vec<Expr>),
    Assign(B<Expr>, B<Expr>),
    Tuple(Vec<Expr>),
    Project(B<Expr>, usize),
    Array(Vec<Expr>),
    Index(B<Expr>, B<Expr>),
    Match(B<Expr>, Vec<(Expr, Expr)>, Option<B<Expr>>),
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
            Literal(value) => writeln!(f, "{indent_str}{value}"),
            Variable(name) => writeln!(f, "{indent_str}{name} (local)"),
            LetVar(name, mutable, expr) => {
                let kw = if *mutable { "mut" } else { "let" };
                writeln!(f, "{indent_str}{kw} {name} =")?;
                expr.format_ind(f, indent + 1)
            }
            Abstract(args, body) => {
                write!(f, "{indent_str}|")?;
                for arg in args {
                    write!(f, "{arg}, ")?;
                }
                writeln!(f, "|")?;
                body.format_ind(f, indent + 1)
            }
            Apply(func, args) => {
                writeln!(f, "{indent_str}eval")?;
                func.format_ind(f, indent + 1)?;
                writeln!(f, "{indent_str}and apply to (")?;
                for arg in args {
                    arg.format_ind(f, indent + 1)?;
                }
                writeln!(f, "{indent_str})")
            }
            StaticApply(func, args) => {
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
            Assign(place, value) => {
                writeln!(f, "{indent_str}=")?;
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
            Project(expr, index) => {
                expr.format_ind(f, indent)?;
                writeln!(f, "{indent_str}.{index}")
            }
            Array(args) => {
                writeln!(f, "{indent_str}[")?;
                for arg in args.iter() {
                    arg.format_ind(f, indent + 1)?;
                }
                writeln!(f, "{indent_str}]")
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
        match &self.kind {
            ExprKind::LetVar(_, _, expr) => expr.acc_errors_rec(errors),
            ExprKind::Abstract(_, expr) => expr.acc_errors_rec(errors),
            ExprKind::Apply(expr, args) => {
                expr.acc_errors_rec(errors);
                acc_errors(errors, args.iter());
            }
            ExprKind::StaticApply(_, args) => acc_errors(errors, args.iter()),
            ExprKind::Block(exprs) => acc_errors(errors, exprs.iter()),
            ExprKind::Assign(place, value) => {
                place.acc_errors_rec(errors);
                value.acc_errors_rec(errors);
            }
            ExprKind::Tuple(args) => acc_errors(errors, args.iter()),
            ExprKind::Project(expr, _) => expr.acc_errors_rec(errors),
            ExprKind::Array(args) => acc_errors(errors, args.iter()),
            ExprKind::Index(expr, index) => {
                expr.acc_errors_rec(errors);
                index.acc_errors_rec(errors);
            }
            ExprKind::Match(expr, cases, default) => {
                expr.acc_errors_rec(errors);
                acc_errors(errors, cases.iter().map(|(_, expr)| expr));
                if let Some(default) = default {
                    default.acc_errors_rec(errors);
                }
            }
            ExprKind::Error(error) => errors.push((error.clone(), self.span)),
            _ => {}
        }
    }
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.format(f)
    }
}

// TODO: add an paths_overlap function that checks whether function call paths overlap
// see page 11 of Implementation Strategies for Mutable Value Semantics
