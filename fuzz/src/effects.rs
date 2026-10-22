// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Generator of programs exercising trait output effects.
//!
//! The grammar targets almost never produce a trait with an output effect together with impls,
//! generic callers and fallible callbacks that agree with each other. This generator builds such
//! programs from fixed building blocks, typed by construction:
//!
//! - traits whose output effect `E` sits in different positions: the method's own row (positive),
//!   a callback parameter's row (negative), both (invariant), or a returned function's row;
//! - concrete impls fixing `E` to `()` or `fallible`, blanket impls over a wrapper forwarding,
//!   extending or constraining the evidence's `E` (possibly of another trait), and impls for a
//!   callback carrier whose `E` comes from the stored callable;
//! - generic callers reaching the methods directly, through declared signatures, method
//!   references, eager and lazy std adaptors, and other callers;
//! - an entry expression summing calls on concrete values, with pure and fallible callbacks.
//!
//! Every program computes an `int`, so outcomes compare as plain values or failure kinds.

use arbitrary::{Result, Unstructured};
use std::fmt::Write;

/// Where a trait's output effect `E` appears in its method.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TraitKind {
    /// `fn m0(s: Self, x: int, f: (int) -> int ! E) -> int ! E`: invariant.
    Both,
    /// `fn m1(s: Self, x: int) -> int ! E`: positive.
    Own,
    /// `fn m2(s: Self, x: int, f: (int) -> int ! E) -> int`: negative.
    Callback,
    /// `fn m3(s: Self) -> ((int) -> int ! E)`: positive, in a returned function.
    Returned,
    /// `fn m4(s: Self, x: int) -> int ! (fallible, E)`: positive, next to a primitive.
    OwnFallible,
}

const KINDS: [TraitKind; 5] = [
    TraitKind::Both,
    TraitKind::Own,
    TraitKind::Callback,
    TraitKind::Returned,
    TraitKind::OwnFallible,
];

impl TraitKind {
    fn index(self) -> usize {
        KINDS.iter().position(|kind| *kind == self).unwrap()
    }

    fn takes_callback(self) -> bool {
        matches!(self, Self::Both | Self::Callback)
    }

    /// Whether `E` only occurs positively, so an impl with fewer effects satisfies a request.
    fn positive(self) -> bool {
        matches!(self, Self::Own | Self::Returned | Self::OwnFallible)
    }
}

/// A concrete effect, as fixed by an impl or carried by a callback.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Eff {
    Pure,
    Fallible,
}

/// How the wrapper `W<T>` implements a trait.
#[derive(Clone, Copy, Debug)]
pub enum WrapImpl {
    /// `! E = E where T: Tr<! E = E>`, delegating to another trait `inner` of the same polarity
    /// shape (equal to the implemented one, or a positive one for a positive trait).
    Forward { inner: TraitKind, variant: u8 },
    /// `! E = (fallible, E) where T: Tr<! E = E>`; positive traits only.
    Extend,
    /// `! E = () where T: Tr<! E = ()>`.
    Pure,
}

/// The impls of one trait.
#[derive(Clone, Debug)]
pub struct TraitImpls {
    pub kind: TraitKind,
    /// Concrete impls for `S0` and `S1`, with their fixed `E` and body variant.
    pub concrete: [Option<(Eff, u8)>; 2],
    pub wrap: Option<WrapImpl>,
    /// Whether the callback carrier `C<! E>` implements the trait (positive traits only).
    pub carrier: bool,
}

/// A concrete value of a self type.
#[derive(Clone, Debug)]
pub enum SelfValue {
    S(usize, i8),
    W(Box<SelfValue>),
    C(Callback),
}

/// A unary `int` callback.
#[derive(Clone, Copy, Debug)]
pub struct Callback {
    pub shape: u8,
    pub constant: i8,
}

const CALLBACK_SHAPES: u8 = 5;

impl Callback {
    fn eff(self) -> Eff {
        match self.shape {
            0..=2 => Eff::Pure,
            _ => Eff::Fallible,
        }
    }

    fn render(self, var: &str) -> String {
        let c = self.constant;
        match self.shape {
            0 => format!("|{var}| {var} + {c}"),
            1 => format!("|{var}| {var} * {c}"),
            2 => format!("|{var}| {c}"),
            3 => format!("|{var}| idiv({c}, {var})"),
            _ => format!("|{var}| idiv({var}, {c})"),
        }
    }
}

/// How a generic caller reaches its method.
#[derive(Clone, Copy, Debug)]
pub enum Flavor {
    Direct,
    /// A declared signature `fn g<T ! E>(s: T, …) where T: Tr<! E = E>`.
    Declared,
    /// Through a local method reference.
    Reference,
    EagerMap,
    EagerFilter,
    LazyMap,
    LazyFold,
    /// Calls an earlier caller on `W(s)`.
    Delegate(usize),
}

/// A generic caller `g<i>`.
#[derive(Clone, Debug)]
pub struct Caller {
    pub kind: TraitKind,
    /// How many wrappers the caller adds before reaching the method.
    pub depth: usize,
    pub flavor: Flavor,
    /// Whether the caller takes an array argument `a` (adaptor flavors, possibly delegated).
    pub takes_array: bool,
}

/// One summand of the entry expression.
#[derive(Clone, Debug)]
pub struct Term {
    /// The caller called, or `None` for a direct method call.
    pub caller: Option<usize>,
    pub kind: TraitKind,
    pub value: SelfValue,
    pub x: i8,
    pub callback: Option<Callback>,
    pub array: Vec<i8>,
}

/// A generated program.
#[derive(Clone, Debug)]
pub struct EffectProgram {
    pub traits: Vec<TraitImpls>,
    pub callers: Vec<Caller>,
    pub terms: Vec<Term>,
}

/// Rendering choices that must not change a program's outcome.
#[derive(Clone, Copy, Debug, Default)]
pub struct Variant {
    /// Effect variables named `Q` instead of `E`.
    pub rename: bool,
    /// Impls and entry terms in reverse order.
    pub reverse: bool,
}

impl EffectProgram {
    pub fn generate(u: &mut Unstructured) -> Result<Self> {
        let mut traits: Vec<TraitImpls> = Vec::new();
        for kind in KINDS {
            if !u.arbitrary::<bool>()? {
                continue;
            }
            let mut concrete = [None, None];
            for slot in &mut concrete {
                if u.ratio(2, 3)? {
                    let eff = if u.arbitrary()? {
                        Eff::Fallible
                    } else {
                        Eff::Pure
                    };
                    *slot = Some((eff, u.int_in_range(0..=1)?));
                }
            }
            traits.push(TraitImpls {
                kind,
                concrete,
                wrap: None,
                carrier: kind.positive() && u.arbitrary()?,
            });
        }
        if traits.is_empty() {
            traits.push(TraitImpls {
                kind: TraitKind::Own,
                concrete: [Some((Eff::Fallible, 0)), Some((Eff::Pure, 0))],
                wrap: None,
                carrier: true,
            });
        }
        // Wrapper impls may delegate to another generated trait, so they are chosen once all
        // traits are known.
        let kinds: Vec<_> = traits.iter().map(|t| t.kind).collect();
        for implementation in &mut traits {
            if !u.ratio(3, 4)? {
                continue;
            }
            let kind = implementation.kind;
            let wrap = match u.int_in_range(0..=3)? {
                0 if kind.positive() => WrapImpl::Extend,
                1 => WrapImpl::Pure,
                2 if kind.positive() => {
                    // Forwarding to `OwnFallible` would add `fallible` to a row declared `E`.
                    let inner: Vec<_> = kinds
                        .iter()
                        .copied()
                        .filter(|k| k.positive() && (*k != TraitKind::OwnFallible || *k == kind))
                        .collect();
                    WrapImpl::Forward {
                        inner: *u.choose(&inner)?,
                        variant: u.int_in_range(0..=1)?,
                    }
                }
                _ => WrapImpl::Forward {
                    inner: kind,
                    variant: u.int_in_range(0..=1)?,
                },
            };
            implementation.wrap = Some(wrap);
        }

        let mut program = EffectProgram {
            traits,
            callers: Vec::new(),
            terms: Vec::new(),
        };

        let caller_count = u.int_in_range(0..=4)?;
        for _ in 0..caller_count {
            let flavor = match u.int_in_range(0..=7)? {
                0 => Flavor::Direct,
                1 => Flavor::Declared,
                2 => Flavor::Reference,
                3 => Flavor::EagerMap,
                4 => Flavor::EagerFilter,
                5 => Flavor::LazyMap,
                6 => Flavor::LazyFold,
                _ if !program.callers.is_empty() => {
                    Flavor::Delegate(u.int_in_range(0..=program.callers.len() - 1)?)
                }
                _ => Flavor::Direct,
            };
            let caller = match flavor {
                Flavor::Delegate(index) => {
                    let callee = &program.callers[index];
                    Caller {
                        kind: callee.kind,
                        depth: callee.depth + 1,
                        flavor,
                        takes_array: callee.takes_array,
                    }
                }
                _ => {
                    let kind = u.choose(&program.traits)?.kind;
                    // A declared signature names the trait's effect in a callback-free form only.
                    let flavor = match flavor {
                        Flavor::Declared if !matches!(kind, TraitKind::Own | TraitKind::Both) => {
                            Flavor::Direct
                        }
                        flavor => flavor,
                    };
                    Caller {
                        kind,
                        depth: 0,
                        flavor,
                        takes_array: matches!(
                            flavor,
                            Flavor::EagerMap
                                | Flavor::EagerFilter
                                | Flavor::LazyMap
                                | Flavor::LazyFold
                        ),
                    }
                }
            };
            program.callers.push(caller);
        }

        let term_count = u.int_in_range(1..=4)?;
        for _ in 0..term_count {
            if let Some(term) = program.term(u)? {
                program.terms.push(term);
            }
        }
        Ok(program)
    }

    fn term(&self, u: &mut Unstructured) -> Result<Option<Term>> {
        let caller = if !self.callers.is_empty() && u.ratio(2, 3)? {
            Some(u.int_in_range(0..=self.callers.len() - 1)?)
        } else {
            None
        };
        let (kind, depth) = match caller {
            Some(index) => (self.callers[index].kind, self.callers[index].depth),
            None => (u.choose(&self.traits)?.kind, 0),
        };
        // Try a few values; give up on this term if none implements the trait.
        for _ in 0..4 {
            let value = self.self_value(u, 3)?;
            let mut reached = value.clone();
            for _ in 0..depth {
                reached = SelfValue::W(Box::new(reached));
            }
            let Some(eff) = self.eff(kind, &reached) else {
                continue;
            };
            let callback = if kind.takes_callback() {
                let callback = arbitrary_callback(u)?;
                // A callback reaching an impl fixing `E = ()` must be pure.
                if eff == Eff::Pure && callback.eff() == Eff::Fallible {
                    continue;
                }
                Some(callback)
            } else {
                None
            };
            let takes_array = caller.is_some_and(|index| self.callers[index].takes_array);
            let array = if takes_array {
                let len = u.int_in_range(0..=3)?;
                (0..len)
                    .map(|_| u.int_in_range(-1..=3))
                    .collect::<Result<_>>()?
            } else {
                Vec::new()
            };
            return Ok(Some(Term {
                caller,
                kind,
                value,
                x: u.int_in_range(-1..=3)?,
                callback,
                array,
            }));
        }
        Ok(None)
    }

    fn self_value(&self, u: &mut Unstructured, depth: usize) -> Result<SelfValue> {
        Ok(match u.int_in_range(0..=3)? {
            2 if depth > 0 => SelfValue::W(Box::new(self.self_value(u, depth - 1)?)),
            3 => SelfValue::C(arbitrary_callback(u)?),
            index => SelfValue::S(index & 1, u.int_in_range(0..=2)?),
        })
    }

    fn implementation(&self, kind: TraitKind) -> Option<&TraitImpls> {
        self.traits.iter().find(|t| t.kind == kind)
    }

    /// The effect `E` that `value` gives the trait `kind`, or `None` if it does not implement it.
    fn eff(&self, kind: TraitKind, value: &SelfValue) -> Option<Eff> {
        let implementation = self.implementation(kind)?;
        match value {
            SelfValue::S(index, _) => implementation.concrete[*index].map(|(eff, _)| eff),
            SelfValue::C(callback) => implementation.carrier.then(|| callback.eff()),
            SelfValue::W(inner) => match implementation.wrap? {
                WrapImpl::Forward {
                    inner: inner_kind, ..
                } => self.eff(inner_kind, inner),
                WrapImpl::Extend => self.eff(kind, inner).map(|_| Eff::Fallible),
                WrapImpl::Pure => (self.eff(kind, inner)? == Eff::Pure).then_some(Eff::Pure),
            },
        }
    }

    /// Renders the program as Ferlium source.
    pub fn render(&self, variant: Variant) -> String {
        let e = if variant.rename { "Q" } else { "E" };
        let mut out = String::new();
        for implementation in &self.traits {
            let kind = implementation.kind;
            let i = kind.index();
            let signature = match kind {
                TraitKind::Both => {
                    format!("fn m{i}(s: Self, x: int, f: (int) -> int ! {e}) -> int ! {e};")
                }
                TraitKind::Own => format!("fn m{i}(s: Self, x: int) -> int ! {e};"),
                TraitKind::Callback => {
                    format!("fn m{i}(s: Self, x: int, f: (int) -> int ! {e}) -> int;")
                }
                TraitKind::Returned => format!("fn m{i}(s: Self) -> ((int) -> int ! {e});"),
                TraitKind::OwnFallible => {
                    format!("fn m{i}(s: Self, x: int) -> int ! (fallible, {e});")
                }
            };
            writeln!(out, "trait Tr{i}<Self |-> ! {e}> {{ {signature} }}").unwrap();
        }
        out.push_str("struct S0 { v: int }\nstruct S1 { v: int }\nstruct W<T>(T)\n");
        writeln!(out, "struct C<! {e}> {{ f: (int) -> int ! {e} }}").unwrap();
        out.push_str(
            "fn total(a: [int]) -> int {\n\tlet mut t = 0;\n\tfor v in a {\n\t\tt = t + v\n\t};\n\tt\n}\n",
        );

        let mut impls = Vec::new();
        for implementation in &self.traits {
            render_impls(implementation, e, &mut impls);
        }
        if variant.reverse {
            impls.reverse();
        }
        for implementation in impls {
            out.push_str(&implementation);
        }

        for (index, caller) in self.callers.iter().enumerate() {
            out.push_str(&self.render_caller(index, caller, e));
        }

        let mut terms: Vec<_> = self
            .terms
            .iter()
            .map(|term| self.render_term(term))
            .collect();
        if variant.reverse {
            terms.reverse();
        }
        if terms.is_empty() {
            out.push_str("0\n");
        } else {
            out.push_str(&terms.join(" + "));
            out.push('\n');
        }
        out
    }

    fn render_caller(&self, index: usize, caller: &Caller, e: &str) -> String {
        let kind = caller.kind;
        let i = kind.index();
        let f_param = if kind.takes_callback() { ", f" } else { "" };
        let a_param = if caller.takes_array { ", a: [int]" } else { "" };
        let call = |s: &str, x: &str| method_call(kind, s, x, "f");
        match caller.flavor {
            Flavor::Direct => {
                format!(
                    "fn g{index}(s, x{f_param}{a_param}) {{ {} }}\n",
                    call("s", "x")
                )
            }
            Flavor::Declared => {
                let f_param = if kind.takes_callback() {
                    format!(", f: (int) -> int ! {e}")
                } else {
                    String::new()
                };
                format!(
                    "fn g{index}<T ! {e}>(s: T, x: int{f_param}) -> int\nwhere\n\tT: Tr{i}<! {e} = {e}>\n{{\n\t{}\n}}\n",
                    call("s", "x")
                )
            }
            Flavor::Reference => {
                let call = method_call_named(kind, "m", "s", "x", "f");
                format!("fn g{index}(s, x{f_param}) {{\n\tlet m = m{i};\n\t{call}\n}}\n")
            }
            Flavor::EagerMap => format!(
                "fn g{index}(s, x{f_param}{a_param}) {{ total(a |> map(|y| {})) + x }}\n",
                call("s", "y")
            ),
            Flavor::EagerFilter => format!(
                "fn g{index}(s, x{f_param}{a_param}) {{ total(a |> filter(|y| {} > x)) }}\n",
                call("s", "y")
            ),
            Flavor::LazyMap => format!(
                "fn g{index}(s, x{f_param}{a_param}) {{ iter(a) |> map(|y| {}) |> count() }}\n",
                call("s", "y")
            ),
            Flavor::LazyFold => format!(
                "fn g{index}(s, x{f_param}{a_param}) {{ fold(iter(a) |> map(|y| {}), x, |acc, v| acc + v) }}\n",
                call("s", "y")
            ),
            Flavor::Delegate(callee) => {
                let f_arg = if kind.takes_callback() { ", f" } else { "" };
                let (a_param, a_arg) = if caller.takes_array {
                    (", a", ", a")
                } else {
                    ("", "")
                };
                format!(
                    "fn g{index}(s, x{f_param}{a_param}) {{ g{callee}(W(s), x{f_arg}{a_arg}) }}\n"
                )
            }
        }
    }

    fn render_term(&self, term: &Term) -> String {
        let value = render_value(&term.value);
        let x = term.x.to_string();
        let f = term.callback.map(|callback| callback.render("z"));
        match term.caller {
            None => method_call(term.kind, &value, &x, f.as_deref().unwrap_or("")),
            Some(index) => {
                let mut args = vec![value, x];
                args.extend(f);
                if self.callers[index].takes_array {
                    let items: Vec<_> = term.array.iter().map(i8::to_string).collect();
                    args.push(format!("[{}]", items.join(", ")));
                }
                format!("g{index}({})", args.join(", "))
            }
        }
    }
}

fn arbitrary_callback(u: &mut Unstructured) -> Result<Callback> {
    Ok(Callback {
        shape: u.int_in_range(0..=CALLBACK_SHAPES - 1)?,
        constant: u.int_in_range(0..=2)?,
    })
}

fn method_call(kind: TraitKind, s: &str, x: &str, f: &str) -> String {
    method_call_named(kind, &format!("m{}", kind.index()), s, x, f)
}

fn method_call_named(kind: TraitKind, m: &str, s: &str, x: &str, f: &str) -> String {
    match kind {
        TraitKind::Both | TraitKind::Callback => format!("{m}({s}, {x}, {f})"),
        TraitKind::Own | TraitKind::OwnFallible => format!("{m}({s}, {x})"),
        TraitKind::Returned => format!("{{ let h = {m}({s}); h({x}) }}"),
    }
}

fn render_value(value: &SelfValue) -> String {
    match value {
        SelfValue::S(index, v) => format!("S{index} {{ v: {v} }}"),
        SelfValue::W(inner) => format!("W({})", render_value(inner)),
        SelfValue::C(callback) => format!("C {{ f: {} }}", callback.render("w")),
    }
}

fn render_impls(implementation: &TraitImpls, e: &str, out: &mut Vec<String>) {
    let kind = implementation.kind;
    let i = kind.index();
    let m = format!("m{i}");
    let params = match kind {
        TraitKind::Both | TraitKind::Callback => "s, x, f",
        TraitKind::Own | TraitKind::OwnFallible => "s, x",
        TraitKind::Returned => "s",
    };
    for (index, concrete) in implementation.concrete.iter().enumerate() {
        let Some((eff, variant)) = *concrete else {
            continue;
        };
        let row = match eff {
            Eff::Pure => "()",
            Eff::Fallible => "fallible",
        };
        let body = concrete_body(kind, eff, variant);
        out.push(format!(
            "impl Tr{i} for <Self = S{index} |-> ! {e} = {row}> {{\n\tfn {m}({params}) {{ {body} }}\n}}\n"
        ));
    }
    if let Some(wrap) = implementation.wrap {
        let (generics, row, bound_trait, bound_row, body) = match wrap {
            WrapImpl::Forward { inner, variant } => {
                let body = forward_body(kind, inner, variant);
                (
                    format!("<T ! {e}>"),
                    e.to_string(),
                    inner.index(),
                    e.to_string(),
                    body,
                )
            }
            WrapImpl::Extend => {
                let body = match kind {
                    TraitKind::Returned => {
                        format!("let h = {m}(s.0);\n\t\t|y| idiv(h(y), 1)")
                    }
                    _ => format!("idiv({}, 1)", method_call(kind, "s.0", "x", "f")),
                };
                (
                    format!("<T ! {e}>"),
                    format!("(fallible, {e})"),
                    i,
                    e.to_string(),
                    body,
                )
            }
            WrapImpl::Pure => {
                let body = match kind {
                    TraitKind::Returned => format!("{m}(s.0)"),
                    _ => method_call(kind, "s.0", "x", "f"),
                };
                (
                    "<T>".to_string(),
                    "()".to_string(),
                    i,
                    "()".to_string(),
                    body,
                )
            }
        };
        out.push(format!(
            "impl{generics} Tr{i} for <Self = W<T> |-> ! {e} = {row}>\nwhere\n\tT: Tr{bound_trait}<! {e} = {bound_row}>\n{{\n\tfn {m}({params}) {{\n\t\t{body}\n\t}}\n}}\n"
        ));
    }
    if implementation.carrier {
        let body = match kind {
            TraitKind::Own => "s.f(x)".to_string(),
            TraitKind::OwnFallible => "idiv(s.f(x), 1)".to_string(),
            TraitKind::Returned => "s.f".to_string(),
            TraitKind::Both | TraitKind::Callback => {
                unreachable!("carriers implement positive traits")
            }
        };
        out.push(format!(
            "impl<! {e}> Tr{i} for <Self = C<! {e}> |-> ! {e} = {e}> {{\n\tfn {m}({params}) {{ {body} }}\n}}\n"
        ));
    }
}

fn concrete_body(kind: TraitKind, eff: Eff, variant: u8) -> String {
    match (kind, eff, variant) {
        (TraitKind::Both, Eff::Pure, 0) => "f(x) + s.v".into(),
        (TraitKind::Both, Eff::Pure, _) => "f(f(x) + s.v)".into(),
        (TraitKind::Both, Eff::Fallible, 0) => "idiv(f(x), s.v)".into(),
        (TraitKind::Both, Eff::Fallible, _) => "f(idiv(x, s.v))".into(),
        (TraitKind::Own, Eff::Pure, 0) => "x + s.v".into(),
        (TraitKind::Own, Eff::Pure, _) => "x * s.v".into(),
        (TraitKind::Own, Eff::Fallible, 0) => "idiv(x, s.v)".into(),
        (TraitKind::Own, Eff::Fallible, _) => "idiv(s.v, x)".into(),
        (TraitKind::Callback, Eff::Pure, 0) => "f(x) + s.v".into(),
        (TraitKind::Callback, Eff::Pure, _) => "f(f(x))".into(),
        // The method's own row is pure: an impl accepting fallible callbacks cannot call them.
        (TraitKind::Callback, Eff::Fallible, _) => "x + s.v".into(),
        (TraitKind::Returned, Eff::Pure, 0) => "|y| y + s.v".into(),
        (TraitKind::Returned, Eff::Pure, _) => "{ let v = s.v; |y| y * v }".into(),
        (TraitKind::Returned, Eff::Fallible, 0) => "|y| idiv(y, s.v)".into(),
        (TraitKind::Returned, Eff::Fallible, _) => "{ let v = s.v; |y| idiv(v, y) }".into(),
        (TraitKind::OwnFallible, _, 0) => "idiv(x, s.v)".into(),
        (TraitKind::OwnFallible, _, _) => "x + s.v".into(),
    }
}

fn forward_body(kind: TraitKind, inner: TraitKind, variant: u8) -> String {
    let m = format!("m{}", inner.index());
    match (kind, inner) {
        (TraitKind::Both | TraitKind::Callback, _) => {
            if variant == 0 {
                format!("{m}(s.0, x, f)")
            } else {
                format!("{m}(s.0, x, |y| f(y) + 1)")
            }
        }
        (TraitKind::Returned, TraitKind::Returned) => {
            if variant == 0 {
                format!("{m}(s.0)")
            } else {
                format!("let h = {m}(s.0);\n\t\t|y| h(y) + 1")
            }
        }
        (TraitKind::Returned, _) => format!("let t = s.0;\n\t\t|y| {m}(t, y)"),
        (_, TraitKind::Returned) => format!("let h = {m}(s.0);\n\t\th(x)"),
        _ => {
            if variant == 0 {
                format!("{m}(s.0, x)")
            } else {
                format!("{m}(s.0, x) + 1")
            }
        }
    }
}
