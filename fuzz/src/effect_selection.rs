// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Generator and oracle for the rule that effects never select an impl.
//!
//! Programs combine impls that use effects in their prerequisites with the callers, derivations
//! and containers through which an effect can reach them. Beyond the soundness checks of
//! `effect_oracle`, the same program with only a callback's annotation changed must not run
//! differently when it compiles in both forms, and declarations that would let effects select
//! an impl must be rejected with the matching error. A pure callback must be accepted wherever
//! no impl asks for an effect.

use crate::effect_oracle::{Outcome, Report, check_source_with_trust};
use arbitrary::{Result, Unstructured};
use std::fmt::Write;

const PRELUDE: &str = r#"trait Run<Self |-> ! E> {
	fn run(x: Self) -> int ! E;
}
struct Cb<! F>(() -> int ! F)
impl<! F> Run for <Self = Cb<! F> |-> ! E = F> {
	fn run(x: Cb<! F>) -> int {
		(x.0)()
	}
}
struct Pair<A, B>(A, B)
struct Outer<T>(T)
struct Named<T> { member: T }
enum Choice<T> { #[default] Nothing, Something(T) }
type Pure = () -> int ! ();
type Failing = () -> int ! fallible;
fn measure(data: DataValue) -> int {
	len(to_string(data))
}
struct V<T>(T)
impl<T> Value for V<T> where T: Value, T: Run<! E = ()> {
	fn eq(x: V<T>, y: V<T>) -> bool { run(x.0) == run(y.0) }
	fn to_string(x: V<T>) -> string { to_string(run(x.0)) }
	fn hash(x: V<T>, state: &mut hasher) { hash(run(x.0), state) }
	fn clone(x: V<T>) -> V<T> { V(x.0) }
	fn drop(x: &mut V<T>) {}
}
"#;

/// Programs are trusted, so that they can implement `Value`.
fn check_source(source: &str) -> Report {
    check_source_with_trust(source, true)
}

/// How the serializer of the wrapper `W<T>` relates to the effect of `T`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Serializer {
    /// Ignores `T`.
    NoCall,
    /// Calls `T`, which must be pure.
    PureRun,
    /// Calls `T`, which may fail.
    FallibleRun,
    /// Leaves the effect of `T` open and does not call it.
    OpenNoCall,
    /// Requires `T` to be serializable, and forwards to it.
    Forward,
    /// Requires a pure `T` through another trait.
    ThroughGate,
    /// No impl: `W<T>` is derived.
    Derived,
}

const SERIALIZERS: [Serializer; 7] = [
    Serializer::NoCall,
    Serializer::PureRun,
    Serializer::FallibleRun,
    Serializer::OpenNoCall,
    Serializer::Forward,
    Serializer::ThroughGate,
    Serializer::Derived,
];

/// A declaration that would let effects select an impl, with the error it must be rejected with.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Forbidden {
    /// An input fixes an effect, through an alias.
    FixedAlias,
    /// An input fixes an effect, nested in a tuple.
    FixedNested,
    /// An input fixes an effect argument.
    FixedArgument,
    /// An input repeats an effect variable.
    Repeated,
    /// Two impls differ by the output effect of a prerequisite.
    OverlapOutputEffect,
    /// Two impls differ by an effect inside the output type of a prerequisite.
    OverlapOutputType,
}

const FORBIDDEN: [Forbidden; 6] = [
    Forbidden::FixedAlias,
    Forbidden::FixedNested,
    Forbidden::FixedArgument,
    Forbidden::Repeated,
    Forbidden::OverlapOutputEffect,
    Forbidden::OverlapOutputType,
];

impl Forbidden {
    fn expected_category(self) -> &'static str {
        match self {
            Self::OverlapOutputEffect | Self::OverlapOutputType => "OverlappingTraitImpls",
            _ => "TraitImplInputRestrictsEffect",
        }
    }

    fn render(self) -> &'static str {
        match self {
            Self::FixedAlias => {
                "struct H<T>(T)
impl Serialize for H<Pure> {
	fn serialize(x: H<Pure>) -> DataValue { serialize(1) }
}
"
            }
            Self::FixedNested => {
                "struct H<T>(T)
impl<A> Serialize for H<(A, Failing)> where A: Value {
	fn serialize(x: H<(A, Failing)>) -> DataValue { serialize(1) }
}
"
            }
            Self::FixedArgument => {
                "struct H<T>(T)
impl Serialize for H<Cb<! fallible>> {
	fn serialize(x: H<Cb<! fallible>>) -> DataValue { serialize(1) }
}
"
            }
            Self::Repeated => {
                "impl<! A> Serialize for Pair<Cb<! A>, Cb<! A>> {
	fn serialize(x: Pair<Cb<! A>, Cb<! A>>) -> DataValue { serialize(1) }
}
"
            }
            Self::OverlapOutputEffect => {
                "struct H<T>(T)
impl<T> Serialize for H<T> where T: Run<! E = ()> {
	fn serialize(x: H<T>) -> DataValue { serialize(1) }
}
impl<T> Serialize for H<T> where T: Run<! E = fallible> {
	fn serialize(x: H<T>) -> DataValue { serialize(2) }
}
"
            }
            Self::OverlapOutputType => {
                "struct H<T>(T)
trait Source<Self |-> Item> { fn source(x: Self) -> Item; }
impl<! A> Source for <Self = Cb<! A> |-> Item = Cb<! A>> {
	fn source(x: Cb<! A>) -> Cb<! A> { x }
}
impl<T> Serialize for H<T> where T: Value, T: Source<Item = Cb<! fallible>> {
	fn serialize(x: H<T>) -> DataValue { serialize(1) }
}
impl<T> Serialize for H<T> where T: Value, T: Source<Item = Cb<! read>> {
	fn serialize(x: H<T>) -> DataValue { serialize(2) }
}
"
            }
        }
    }
}

/// What holds the callback when it reaches the serializer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Container {
    Bare,
    Tuple,
    Record,
    Named,
    Array,
    EnumVariant,
    Nested,
}

const CONTAINERS: [Container; 7] = [
    Container::Bare,
    Container::Tuple,
    Container::Record,
    Container::Named,
    Container::Array,
    Container::EnumVariant,
    Container::Nested,
];

/// How the function that needs the impl receives the callback.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Caller {
    /// At the top level, no function.
    Direct,
    /// `fn f(g)`.
    Inferred,
    /// `fn f(g: () -> int)`.
    Partial,
    /// `fn f<! E>(g: () -> int ! E)`.
    Written,
}

const CALLERS: [Caller; 4] = [
    Caller::Direct,
    Caller::Inferred,
    Caller::Partial,
    Caller::Written,
];

/// The body of the callback.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Body {
    Pure,
    Succeeds,
    Fails,
    Writes,
    Reads,
}

const BODIES: [Body; 5] = [
    Body::Pure,
    Body::Succeeds,
    Body::Fails,
    Body::Writes,
    Body::Reads,
];

impl Body {
    fn render(self) -> &'static str {
        match self {
            Self::Pure => "|| 5",
            Self::Succeeds => "|| idiv(4, 2)",
            Self::Fails => "|| idiv(1, 0)",
            Self::Writes => "|| { effects::write(); 5 }",
            Self::Reads => "|| effects::read()",
        }
    }

    /// The annotations this body accepts, from its least row on.
    fn rows(self) -> &'static [&'static str] {
        match self {
            Self::Pure => &["", "()", "fallible", "read", "(fallible, read)"],
            Self::Succeeds | Self::Fails => &["", "fallible", "(fallible, read)"],
            Self::Writes => &["", "write", "(fallible, write)"],
            Self::Reads => &["", "read", "(fallible, read)"],
        }
    }
}

/// What the entry computes with the container.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Use {
    /// Serializes the container.
    Serialize,
    /// Serializes a pair of two callbacks, which needs them to have one type.
    SamePair,
    /// Calls through an impl on `Pair<T, T>` exposing the shared effect.
    RunPair,
    /// Calls through an effect-polymorphic impl.
    RunDirect,
    /// Renders the container through a custom `Value` impl that calls a pure callback.
    Render,
}

const USES: [Use; 5] = [
    Use::Serialize,
    Use::SamePair,
    Use::RunPair,
    Use::RunDirect,
    Use::Render,
];

/// A generated program.
#[derive(Clone, Copy, Debug)]
pub struct SelectionProgram {
    pub serializer: Serializer,
    /// Whether `Cb` has a serializer of its own, which derivation may reach.
    pub serializable_callback: bool,
    pub container: Container,
    pub caller: Caller,
    pub body: Body,
    /// Index into the annotations of `body`.
    pub row: usize,
    pub second_body: Body,
    pub usage: Use,
    /// A pure use of the same application before the entry, to warm caches.
    pub warm: bool,
    pub forbidden: Option<Forbidden>,
}

fn pick<T: Copy>(u: &mut Unstructured, choices: &[T]) -> Result<T> {
    Ok(*u.choose(choices)?)
}

impl SelectionProgram {
    pub fn generate(u: &mut Unstructured) -> Result<Self> {
        let body = pick(u, &BODIES)?;
        Ok(Self {
            serializer: pick(u, &SERIALIZERS)?,
            serializable_callback: u.arbitrary()?,
            container: pick(u, &CONTAINERS)?,
            caller: pick(u, &CALLERS)?,
            body,
            row: u.int_in_range(0..=body.rows().len() - 1)?,
            second_body: pick(u, &BODIES)?,
            usage: pick(u, &USES)?,
            warm: u.arbitrary()?,
            forbidden: if u.ratio(1, 8)? {
                Some(pick(u, &FORBIDDEN)?)
            } else {
                None
            },
        })
    }

    fn serializer_impl(&self) -> &'static str {
        match self.serializer {
            Serializer::NoCall => {
                "impl<T> Serialize for W<T> where T: Value {
	fn serialize(x: W<T>) -> DataValue { serialize(1) }
}
"
            }
            Serializer::PureRun => {
                "impl<T> Serialize for W<T> where T: Run<! E = ()> {
	fn serialize(x: W<T>) -> DataValue { serialize(run(x.0)) }
}
"
            }
            Serializer::FallibleRun => {
                "impl<T> Serialize for W<T> where T: Run<! E = fallible> {
	fn serialize(x: W<T>) -> DataValue { serialize(run(x.0)) }
}
"
            }
            Serializer::OpenNoCall => {
                "impl<T ! F> Serialize for W<T> where T: Run<! E = F> {
	fn serialize(x: W<T>) -> DataValue { serialize(2) }
}
"
            }
            Serializer::Forward => {
                "impl<T> Serialize for W<T> where T: Serialize {
	fn serialize(x: W<T>) -> DataValue { serialize(x.0) }
}
"
            }
            Serializer::ThroughGate => {
                "trait Gate<Self> { fn gate(x: Self) -> int; }
impl<T> Gate for T where T: Run<! E = ()> {
	fn gate(x: T) -> int { run(x) }
}
impl<T> Serialize for W<T> where T: Gate {
	fn serialize(x: W<T>) -> DataValue { serialize(gate(x.0)) }
}
"
            }
            Serializer::Derived => "",
        }
    }

    fn contained(&self, value: &str) -> String {
        match self.container {
            Container::Bare => value.to_string(),
            Container::Tuple => format!("({value},)"),
            Container::Record => format!("{{ a: {value} }}"),
            Container::Named => format!("Named {{ member: {value} }}"),
            Container::Array => format!("[{value}]"),
            Container::EnumVariant => format!("Choice::Something({value})"),
            Container::Nested => format!("(({value}, 1), {{ b: 2 }})"),
        }
    }

    /// The expression over callbacks `a` and `b`.
    fn usage(&self, a: &str, b: &str) -> String {
        match self.usage {
            Use::Serialize => {
                let value = self.contained(&format!("W(Cb({a}))"));
                format!("measure(serialize({value}))")
            }
            Use::SamePair => format!("measure(serialize(Pair(Cb({a}), Cb({b}))))"),
            Use::RunPair => format!("run_pair(Pair(Cb({a}), Cb({b})))"),
            Use::RunDirect => format!("run(Cb({a}))"),
            Use::Render => {
                let value = self.contained(&format!("V(Cb({a}))"));
                format!("len(to_string({value}))")
            }
        }
    }

    /// Renders the program with annotation `row` on the first callback.
    pub fn render_with_row(&self, row: &str, reverse: bool) -> String {
        let mut decls = vec![
            "struct W<T>(T)\n".to_string(),
            self.serializer_impl().to_string(),
            "trait RunPair<Self |-> ! E> { fn run_pair(x: Self) -> int ! E; }
impl<T ! F> RunPair for <Self = Pair<T, T> |-> ! E = F> where T: Run<! E = F> {
	fn run_pair(x: Pair<T, T>) -> int { run(x.0) + run(x.1) }
}
"
            .to_string(),
            "impl<T> Serialize for Pair<T, T> where T: Value {
	fn serialize(x: Pair<T, T>) -> DataValue { serialize(3) }
}
"
            .to_string(),
        ];
        if self.serializable_callback {
            decls.push(
                "impl<! F> Serialize for Cb<! F> {
	fn serialize(x: Cb<! F>) -> DataValue { serialize(9) }
}
"
                .to_string(),
            );
        }
        if let Some(forbidden) = self.forbidden {
            decls.push(forbidden.render().to_string());
        }
        if self.warm {
            let warm = self.usage("|| 7", "|| 8");
            decls.push(format!("fn warm() -> int {{\n\t{warm}\n}}\n"));
        }
        let mut function = match self.caller {
            Caller::Direct => String::new(),
            Caller::Inferred => format!("fn f(g) {{\n\t{}\n}}\n", self.usage("g", "g2()")),
            Caller::Partial => format!(
                "fn f(g: () -> int) -> int {{\n\t{}\n}}\n",
                self.usage("g", "g2()")
            ),
            Caller::Written => format!(
                "fn f<! E>(g: () -> int ! E) -> int {{\n\t{}\n}}\n",
                self.usage("g", "g2()")
            ),
        };
        if !function.is_empty() {
            function.insert_str(0, "fn g2() -> (() -> int) {\n\t|| 6\n}\n");
            decls.push(function);
        }
        if reverse {
            decls.reverse();
        }
        let mut out = PRELUDE.to_string();
        for decl in decls {
            out.push_str(&decl);
        }
        let annotation = if row.is_empty() {
            String::new()
        } else {
            format!(": () -> int ! {row}")
        };
        writeln!(out, "let callback{annotation} = {};", self.body.render()).unwrap();
        let second = self.second_body.render();
        let entry = match self.caller {
            Caller::Direct => self.usage("callback", second),
            _ => "f(callback)".to_string(),
        };
        let warm_call = if self.warm { "warm() + " } else { "" };
        writeln!(out, "{warm_call}{entry}").unwrap();
        out
    }

    pub fn render(&self) -> String {
        self.render_with_row(self.body.rows()[self.row], false)
    }

    /// Whether a pure callback, at the top level and annotated at most as pure, must be
    /// accepted: every impl it reaches exists and asks for no effect.
    fn must_accept(&self) -> bool {
        let pure_callback =
            self.body == Body::Pure && matches!(self.body.rows()[self.row], "" | "()");
        let effect_free_use = match self.usage {
            Use::Serialize => match self.serializer {
                Serializer::FallibleRun => false,
                // Serializing the callback needs a serializer for `Cb`.
                Serializer::Forward | Serializer::Derived => self.serializable_callback,
                Serializer::NoCall
                | Serializer::PureRun
                | Serializer::OpenNoCall
                | Serializer::ThroughGate => true,
            },
            Use::SamePair | Use::RunPair | Use::RunDirect | Use::Render => true,
        };
        self.forbidden.is_none()
            && self.caller == Caller::Direct
            && pure_callback
            && effect_free_use
    }
}

fn same_outcome(a: &Outcome, b: &Outcome) -> bool {
    *a == Outcome::Limit || *b == Outcome::Limit || a == b
}

/// Checks a program; panics on a finding.
pub fn check_selection(program: &SelectionProgram) -> Report {
    let row = program.body.rows()[program.row];
    let source = program.render_with_row(row, false);
    let report = check_source(&source);

    // A declaration that would let effects select an impl never compiles.
    if let Some(forbidden) = program.forbidden {
        match &report {
            Report::Rejected { category, .. } if category == forbidden.expected_category() => {}
            other => panic!(
                "{forbidden:?} must be rejected with {}, got {other:?}:\n{source}",
                forbidden.expected_category()
            ),
        }
        return report;
    }

    // A pure callback is accepted where no impl asks for an effect.
    if program.must_accept() {
        assert!(
            matches!(report, Report::Ran { .. }),
            "a pure callback must be accepted, got {report:?}:\n{source}"
        );
    }

    // Declaration order changes nothing.
    let reversed_source = program.render_with_row(row, true);
    match (&report, &check_source(&reversed_source)) {
        (Report::Rejected { .. }, Report::Rejected { .. }) => {}
        (Report::Ran { outcome: a, .. }, Report::Ran { outcome: b, .. }) => assert!(
            same_outcome(a, b),
            "declaration order changed the outcome ({a:?} versus {b:?}):\n{source}\nreversed:\n{reversed_source}"
        ),
        (a, b) => panic!(
            "declaration order changed whether this compiles ({a:?} versus {b:?}):\n{source}\nreversed:\n{reversed_source}"
        ),
    }

    // An annotation is an upper bound: it cannot change what runs.
    if let Report::Ran { outcome, .. } = &report {
        for other_row in program.body.rows() {
            if *other_row == row {
                continue;
            }
            let other_source = program.render_with_row(other_row, false);
            if let Report::Ran {
                outcome: other_outcome,
                ..
            } = check_source(&other_source)
            {
                assert!(
                    same_outcome(outcome, &other_outcome),
                    "an annotation changed the outcome ({outcome:?} versus {other_outcome:?}):\n{source}\nother:\n{other_source}"
                );
            }
        }
    }
    report
}
