use enum_as_inner::EnumAsInner;
use itertools::Itertools;
use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
};

use ustr::Ustr;

use crate::{
    containers::B,
    error::LocatedError,
    format::write_with_separator,
    module::FmtWithModuleEnv,
    mutability::MutVal,
    r#type::Type,
    value::{LiteralValue, Value},
    Location,
};

/// A spanned Ustr
pub type UstrSpan = (Ustr, Location);

#[derive(Debug, Clone)]
pub struct ModuleFunction {
    pub name: UstrSpan,
    pub args: Vec<UstrSpan>,
    pub args_span: Location,
    pub body: B<Expr>,
    pub span: Location,
}
impl ModuleFunction {
    pub fn new(
        name: UstrSpan,
        args: Vec<UstrSpan>,
        args_span: Location,
        body: B<Expr>,
        span: Location,
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

/// A node of a function dependency graph
#[derive(Debug)]
pub struct FnDepGraphNode(Vec<usize>);
impl crate::graph::Node for FnDepGraphNode {
    type Index = usize;
    fn neighbors(&self) -> impl Iterator<Item = Self::Index> {
        self.0.iter().copied()
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
        name: UstrSpan,
        args: Vec<UstrSpan>,
        args_span: Location,
        body: Expr,
        span: Location,
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

    pub fn merge(mut self, other: Self) -> Self {
        self.extend(other);
        self
    }

    pub fn errors(&self) -> Vec<LocatedError> {
        let mut collector = ErrorCollector::default();
        for ModuleFunction { body, .. } in self.functions.iter() {
            body.visit(&mut collector);
        }
        collector.0
    }

    pub fn is_empty(&self) -> bool {
        self.functions.is_empty() && self.types.is_empty()
    }

    pub fn get_function_dependencies(&self) -> Vec<FnDepGraphNode> {
        let fn_map = self
            .functions
            .iter()
            .enumerate()
            .map(|(index, func)| (func.name.0, index))
            .collect::<HashMap<_, _>>();
        self.functions
            .iter()
            .map(|func| {
                let dependencies = func.body.get_function_dependencies(&fn_map);
                FnDepGraphNode(dependencies.into_iter().collect())
            })
            .collect()
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

/// The kind-specific part of an expression as an Abstract Syntax Tree
#[derive(Debug, Clone, EnumAsInner)]
pub enum ExprKind {
    Literal(Value, Type),
    FormattedString(String),
    /// A variable, or a function from the module environment, or a null-ary variant constructor
    Identifier(Ustr),
    Let(UstrSpan, MutVal, B<Expr>),
    Abstract(Vec<UstrSpan>, B<Expr>),
    Apply(B<Expr>, Vec<Expr>),
    Block(Vec<Expr>),
    Assign(B<Expr>, Location, B<Expr>),
    PropertyPath(Ustr, Ustr),
    Tuple(Vec<Expr>),
    Project(B<Expr>, (usize, Location)),
    Record(Vec<(UstrSpan, Expr)>),
    FieldAccess(B<Expr>, UstrSpan),
    Array(Vec<Expr>),
    Index(B<Expr>, B<Expr>),
    Match(B<Expr>, Vec<(Pattern, Expr)>, Option<B<Expr>>),
    ForLoop(UstrSpan, B<Expr>, B<Expr>),
    Error,
}

/// An expression as an Abstract Syntax Tree
#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Location,
}
impl Expr {
    pub fn new(kind: ExprKind, span: Location) -> Self {
        Self { kind, span }
    }

    pub fn format_ind(&self, f: &mut std::fmt::Formatter, indent: usize) -> std::fmt::Result {
        let indent_str = "  ".repeat(indent);
        use ExprKind::*;
        match &self.kind {
            Literal(value, _) => writeln!(f, "{indent_str}{value}"),
            FormattedString(string) => writeln!(f, "{indent_str}f\"{string}\""),
            Identifier(name) => writeln!(f, "{indent_str}{name} (local)"),
            Let((name, _), mutable, expr) => {
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
            Project(expr, (index, _)) => {
                expr.format_ind(f, indent)?;
                writeln!(f, "{indent_str}  .{index}")
            }
            Record(fields) => {
                writeln!(f, "{indent_str}{{")?;
                for ((name, _), value) in fields.iter() {
                    writeln!(f, "{indent_str}  {name}:")?;
                    value.format_ind(f, indent + 2)?;
                    writeln!(f, "{indent_str}  ,")?;
                }
                writeln!(f, "{indent_str}}}")
            }
            FieldAccess(expr, (field, _)) => {
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
            PropertyPath(scope, name) => writeln!(f, "{indent_str}@{}.{}", scope, name),
            Error => writeln!(f, "{indent_str}Error"),
        }
    }

    pub fn format(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.format_ind(f, 0)
    }

    fn get_function_dependencies(&self, fn_map: &HashMap<Ustr, usize>) -> HashSet<usize> {
        struct DependencyCollector<'a> {
            fn_map: &'a HashMap<Ustr, usize>,
            dependencies: HashSet<usize>,
            locals: Vec<Ustr>,
            local_sizes: Vec<usize>,
            local_bases: Vec<usize>,
        }
        use ExprKind::*;
        impl ExprVisitor for DependencyCollector<'_> {
            fn visit_start(&mut self, expr: &Expr) {
                match &expr.kind {
                    Identifier(name) => {
                        let skip = self.local_bases.last().copied().unwrap_or(0);
                        if self
                            .locals
                            .iter()
                            .skip(skip)
                            .rev()
                            .any(|local| local == name)
                        {
                            // this is a local variable shadowing function definition
                        } else if let Some(index) = self.fn_map.get(name) {
                            self.dependencies.insert(*index);
                        }
                    }
                    Abstract(args, _) => {
                        self.local_bases.push(self.locals.len());
                        self.locals.extend(args.iter().map(|(name, _)| *name));
                    }
                    Block(_) => {
                        self.local_sizes.push(self.locals.len());
                    }
                    _ => {}
                }
            }
            fn visit_end(&mut self, expr: &Expr) {
                match &expr.kind {
                    Let((name, _), _, expr) => {
                        expr.visit(self);
                        self.locals.push(*name);
                    }
                    Abstract(args, _) => {
                        self.local_bases.pop().unwrap();
                        self.locals.truncate(self.locals.len() - args.len());
                    }
                    Block(_) => {
                        let size = self.local_sizes.pop().unwrap();
                        self.locals.truncate(size);
                    }
                    _ => {}
                }
            }
        }
        let mut collector = DependencyCollector {
            fn_map,
            dependencies: HashSet::new(),
            locals: Vec::new(),
            local_sizes: Vec::new(),
            local_bases: Vec::new(),
        };
        self.visit(&mut collector);
        collector.dependencies
    }

    /// Visit all nodes of the expression tree
    fn visit(&self, visitor: &mut impl ExprVisitor) {
        visitor.visit_start(self);
        use ExprKind::*;
        match &self.kind {
            Let(_, _, expr) => expr.visit(visitor),
            Abstract(_, expr) => expr.visit(visitor),
            Apply(expr, args) => {
                expr.visit(visitor);
                visitor.visit_exprs(args.iter());
            }
            Block(exprs) => visitor.visit_exprs(exprs.iter()),
            Assign(place, _, value) => {
                place.visit(visitor);
                value.visit(visitor);
            }
            Tuple(args) => visitor.visit_exprs(args.iter()),
            Project(expr, _) => expr.visit(visitor),
            Record(fields) => visitor.visit_exprs(fields.iter().map(|(_, expr)| expr)),
            FieldAccess(expr, _) => expr.visit(visitor),
            Array(args) => visitor.visit_exprs(args.iter()),
            Index(expr, index) => {
                expr.visit(visitor);
                index.visit(visitor);
            }
            Match(expr, cases, default) => {
                expr.visit(visitor);
                visitor.visit_exprs(cases.iter().map(|(_, expr)| expr));
                if let Some(default) = default {
                    default.visit(visitor);
                }
            }
            ForLoop(_, iterator, body) => {
                iterator.visit(visitor);
                body.visit(visitor);
            }
            _ => {}
        }
        visitor.visit_end(self);
    }

    // TODO: use the visitor to collect the dependency graph
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.format(f)
    }
}

/// A visitor pattern for expressions
pub trait ExprVisitor {
    fn visit_start(&mut self, _expr: &Expr) {}
    fn visit_end(&mut self, _expr: &Expr) {}

    fn visit_exprs<'e>(&mut self, exprs: impl Iterator<Item = &'e Expr>)
    where
        Self: Sized,
    {
        for expr in exprs {
            expr.visit(self);
        }
    }
}

#[derive(Default)]
struct ErrorCollector(Vec<LocatedError>);
impl ExprVisitor for ErrorCollector {
    fn visit_start(&mut self, expr: &Expr) {
        if let ExprKind::Error = expr.kind {
            self.0.push(("parse error".into(), expr.span));
        }
    }
}

/// The kind-specific part of an expression as an Abstract Syntax Tree
#[derive(Debug, Clone, EnumAsInner)]
pub enum PatternKind {
    Literal(LiteralValue, Type),
    Variant { tag: UstrSpan, vars: Vec<UstrSpan> },
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
    pub span: Location,
}

impl Pattern {
    pub fn new(kind: PatternKind, span: Location) -> Self {
        Self { kind, span }
    }

    pub fn format_ind(&self, f: &mut std::fmt::Formatter, indent: usize) -> std::fmt::Result {
        let indent_str = "  ".repeat(indent);
        use PatternKind::*;
        match &self.kind {
            Literal(value, _) => writeln!(f, "{indent_str}{value}"),
            Variant { tag, vars, .. } => {
                write!(f, "{indent_str}{} ", tag.0)?;
                if !vars.is_empty() {
                    write!(f, "(")?;
                    write_with_separator(vars.iter().map(|(var, _)| var), ", ", f)?;
                    writeln!(f, ")")
                } else {
                    writeln!(f)
                }
            }
            Error(s) => writeln!(f, "{indent_str}Pattern error: {s}"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PropertyAccess {
    Get,
    Set,
}
impl PropertyAccess {
    pub fn as_prefix(&self) -> &'static str {
        use PropertyAccess::*;
        match self {
            Get => "get",
            Set => "set",
        }
    }
}
