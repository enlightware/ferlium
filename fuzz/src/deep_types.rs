// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Generator of deep and large types and definitions, for the compiler's limits.
//!
//! Source that nests one level can still make the compiler derive deep or exponentially large
//! types. This generator chains and doubles the shapes that do so, each built on the previous ones:
//!
//! - wrappers, pairs, nested one-element tuples, and instances of a struct holding its parameter
//!   twice;
//! - structs and enums holding earlier types, and instances of generic structs;
//! - recursive groups of enums, generic or not, each member holding the next once or twice, and
//!   recursive groups of structural aliases;
//! - functions applying the previous one twice, whose inferred types double, and functions passing
//!   a pair of their argument to the previous one, whose values double.
//!
//! Each step repeats its shape up to a few hundred times, so that chains reach past the limits. A
//! program builds a value of each type in sequence, matches the variants among them, and compares
//! the last one with itself, also after some of: passing it through functions, an array, a
//! closure, assignments, a loop or a generic enum, so every program computes an `int`. The
//! compiler must accept it, or reject it with one of its limits, and every backend must agree on
//! its outcome; the fuzzer bounds its time and memory.

use crate::effect_oracle::{Outcome, Report, check_source};
use arbitrary::{Result, Unstructured};
use std::{fmt::Write, num::NonZeroU16};

/// The definitions that the steps and the uses of the last value build on.
const PRELUDE: &str = r#"struct W<T>(T)
struct P<T> { a: T, b: T }
enum Opt<T> { Some(T), None }
fn same<X>(x: X) -> X { x }
fn both<A, B>(a: A, b: B) -> (A, B) { (a, b) }
"#;

/// A shape built from earlier types, `a` and `b`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Shape {
    /// `W<a>`.
    Wrap,
    /// `(a, b)`.
    Pair,
    /// `P<a>`, holding `a` twice.
    Doubled,
    /// `a` in `height` nested one-element tuples.
    Tuple { height: u8 },
    /// `struct S { x: a, y: b }`.
    Struct,
    /// `enum E { A(a), B(b), N }`.
    Enum,
    /// `G<a>`, with `struct G<X> { x: X, n: int }`.
    Generic,
    /// A ring of `members` enums, each holding the next one, or twice when `twice`, and `a`;
    /// generic in what it holds when `generic`.
    Ring {
        members: NonZeroU16,
        twice: bool,
        generic: bool,
    },
    /// A ring of `members` structural aliases, each a variant holding the next one or `a`.
    AliasRing { members: NonZeroU16 },
}

/// A shape, repeated: each repetition takes the previous one as `a`.
#[derive(Clone, Debug)]
pub struct Step {
    pub shape: Shape,
    pub repeat: NonZeroU16,
    /// Indices of `a` and `b` among the types built before this step, `int` being the first.
    pub a: usize,
    pub b: usize,
}

/// Functions whose types or values double at each one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Doubling {
    /// `fn hI(x) { hI-1(hI-1(x)) }` from `fn h0(x) { (x, x) }`: the type of `hK(1)` has 2^(2^K)
    /// parts.
    Types { count: u8 },
    /// `fn gI(x) { gI-1((x, x)) }` from `fn g0(x) { 0 }`: `gK(1)` builds a value of 2^K parts,
    /// at run time too, through generic code that the limits do not see, so `K` stays within what
    /// every backend runs.
    Values { count: u8 },
}

#[derive(Clone, Debug)]
pub struct DeepProgram {
    pub steps: Vec<Step>,
    pub doubling: Option<Doubling>,
    /// Which of [`USES`] the last value goes through, one bit each.
    pub uses: u16,
}

/// The ways the last value is used besides being compared with itself: each a definition, the
/// statements before the comparison, and a condition, written with `{last}` for the value and
/// `{ty}` for its type.
const USES: [(&str, &str, &str); 9] = [
    ("", "", "same({last}) == {last}"),
    (
        "fn take(x: {ty}) -> {ty} { x }\n",
        "",
        "take({last}) == {last}",
    ),
    ("", "\tlet held = [{last}, {last}];\n", "held[1] == {last}"),
    ("", "\tlet captured = || {last};\n", "captured() == {last}"),
    (
        "",
        "\tlet mut assigned = {last};\n\tassigned = same({last});\n",
        "assigned == {last}",
    ),
    (
        "",
        "\tlet mut looped = {last};\n\tfor i in 0..3 {\n\t\tlooped = same(looped)\n\t};\n",
        "looped == {last}",
    ),
    (
        "",
        "\tlet wrapped = Opt::Some({last});\n",
        "(match wrapped { Some(x) => x == {last}, None => false })",
    ),
    ("", "\tlet shown = to_string({last});\n", "len(shown) > 0"),
    (
        "",
        "\tlet record = { a: {last}, b: 1 };\n",
        "record.a == {last} and both({last}, 1).0 == {last}",
    ),
];

/// A count, most often small, sometimes past the limits.
fn count(u: &mut Unstructured, small: u16, large: u16) -> Result<NonZeroU16> {
    let count = if u.ratio(1, 4)? {
        u.int_in_range(1..=large)?
    } else {
        u.int_in_range(1..=small)?
    };
    Ok(NonZeroU16::new(count).expect("a count starts at one"))
}

impl DeepProgram {
    pub fn generate(u: &mut Unstructured) -> Result<Self> {
        let step_count = u.int_in_range(1..=6)?;
        let mut steps = Vec::with_capacity(step_count);
        // The number of types built before each step, `int` being the first.
        for built in 1..=step_count {
            let shape = match u.int_in_range(0..=8)? {
                0 => Shape::Wrap,
                1 => Shape::Pair,
                2 => Shape::Doubled,
                3 => Shape::Tuple {
                    height: u.int_in_range(1..=8)?,
                },
                4 => Shape::Struct,
                5 => Shape::Enum,
                6 => Shape::Generic,
                7 => Shape::Ring {
                    members: count(u, 8, 100)?,
                    twice: u.arbitrary()?,
                    generic: u.arbitrary()?,
                },
                _ => Shape::AliasRing {
                    members: count(u, 8, 100)?,
                },
            };
            // A ring is large already: repeat it less.
            let repeat = match shape {
                Shape::Ring { .. } | Shape::AliasRing { .. } => count(u, 2, 8)?,
                _ => count(u, 16, 300)?,
            };
            let a = u.int_in_range(0..=built - 1)?;
            let b = u.int_in_range(0..=built - 1)?;
            steps.push(Step {
                shape,
                repeat,
                a,
                b,
            });
        }
        let doubling = match u.int_in_range(0..=3)? {
            0 => Some(Doubling::Types {
                count: u.int_in_range(1..=6)?,
            }),
            1 => Some(Doubling::Values {
                count: u.int_in_range(1..=12)?,
            }),
            _ => None,
        };
        Ok(Self {
            steps,
            doubling,
            uses: u.arbitrary()?,
        })
    }

    pub fn render(&self) -> String {
        let mut defs = String::from(PRELUDE);
        let mut body = String::from("\tlet v0 = 1;\n");
        // The type and value of each step's result, `int` and `v0` first.
        let mut results = vec![("int".to_string(), "v0".to_string())];
        // Matches on the results of the steps that build variants.
        let mut matches = Vec::new();
        for (s, step) in self.steps.iter().enumerate() {
            let (mut a_ty, mut a_val) = results[step.a].clone();
            let (b_ty, b_val) = results[step.b].clone();
            if step.shape == Shape::Generic {
                writeln!(defs, "struct G{s}<X> {{ x: X, n: int }}").unwrap();
            }
            for r in 0..step.repeat.get() {
                let name = format!("D{s}_{r}");
                let value = format!("v{s}_{r}");
                let built = render_shape(
                    step.shape, &name, &a_ty, &a_val, &b_ty, &b_val, s, &mut defs,
                );
                writeln!(body, "\tlet {value}: {name} = {built};").unwrap();
                if r + 1 == step.repeat.get() {
                    matches.extend(render_match(step.shape, &name, &value));
                }
                a_ty = name;
                a_val = value;
            }
            results.push((a_ty, a_val));
        }
        let (last_ty, last) = results.last().expect("int is always built");
        // Through some of the uses, which put the value in functions, containers, a closure,
        // assignments, a loop or a string.
        let mut uses = format!("{last} == {last}");
        for (index, (def, statements, condition)) in USES.iter().enumerate() {
            if self.uses & (1 << index) == 0 {
                continue;
            }
            let fill = |text: &str| text.replace("{last}", last).replace("{ty}", last_ty);
            defs.push_str(&fill(def));
            body.push_str(&fill(statements));
            write!(uses, " and {}", fill(condition)).unwrap();
        }
        for matched in matches {
            write!(uses, " and {matched}").unwrap();
        }
        match self.doubling {
            Some(Doubling::Types { count }) => {
                defs.push_str("fn h0(x) { (x, x) }\n");
                for i in 1..=count {
                    writeln!(defs, "fn h{i}(x) {{ h{p}(h{p}(x)) }}", p = i - 1).unwrap();
                }
                writeln!(body, "\tlet hv = h{count}(1);").unwrap();
                uses.push_str(" and hv == hv");
            }
            Some(Doubling::Values { count }) => {
                defs.push_str("fn g0(x) { 0 }\n");
                for i in 1..=count {
                    writeln!(defs, "fn g{i}(x) {{ g{p}((x, x)) }}", p = i - 1).unwrap();
                }
                writeln!(body, "\tlet gv = g{count}(1);").unwrap();
                uses.push_str(" and gv == 0");
            }
            None => {}
        }
        format!(
            "{defs}fn f() -> int {{\n{body}\tif {uses} {{\n\t\t1\n\t}} else {{\n\t\t0\n\t}}\n}}\nf()\n"
        )
    }
}

/// Declares the type `name` of `shape` in `defs`, and gives the expression building a value of it.
#[allow(clippy::too_many_arguments)]
fn render_shape(
    shape: Shape,
    name: &str,
    a_ty: &str,
    a_val: &str,
    b_ty: &str,
    b_val: &str,
    step: usize,
    defs: &mut String,
) -> String {
    match shape {
        Shape::Wrap => {
            writeln!(defs, "type {name} = W<{a_ty}>;").unwrap();
            format!("W({a_val})")
        }
        Shape::Pair => {
            writeln!(defs, "type {name} = ({a_ty}, {b_ty});").unwrap();
            format!("({a_val}, {b_val})")
        }
        Shape::Doubled => {
            writeln!(defs, "type {name} = P<{a_ty}>;").unwrap();
            format!("P {{ a: {a_val}, b: {a_val} }}")
        }
        Shape::Tuple { height } => {
            let height = height as usize;
            let ty = format!("{}{a_ty}{}", "(".repeat(height), ",)".repeat(height));
            writeln!(defs, "type {name} = {ty};").unwrap();
            format!("{}{a_val}{}", "(".repeat(height), ",)".repeat(height))
        }
        Shape::Struct => {
            writeln!(defs, "struct {name} {{ x: {a_ty}, y: {b_ty} }}").unwrap();
            format!("{name} {{ x: {a_val}, y: {b_val} }}")
        }
        Shape::Enum => {
            writeln!(defs, "enum {name} {{ A({a_ty}), B({b_ty}), N }}").unwrap();
            format!("{name}::A({a_val})")
        }
        Shape::Generic => {
            writeln!(defs, "type {name} = G{step}<{a_ty}>;").unwrap();
            format!("G{step} {{ x: {a_val}, n: 1 }}")
        }
        Shape::Ring {
            members,
            twice,
            generic,
        } => {
            let members = usize::from(members.get());
            let (params, held) = if generic { ("<X>", "X") } else { ("", a_ty) };
            for i in 0..members {
                let next = format!("{name}R{}{params}", (i + 1) % members);
                let next = if twice {
                    format!("{next}, {next}")
                } else {
                    next
                };
                writeln!(defs, "enum {name}R{i}{params} {{ A({next}), N({held}) }}").unwrap();
            }
            if generic {
                writeln!(defs, "type {name} = {name}R0<{a_ty}>;").unwrap();
            } else {
                writeln!(defs, "type {name} = {name}R0;").unwrap();
            }
            // Two levels deep: the first member holding the second, which holds `a`.
            let second = format!("{name}R{}::N({a_val})", 1 % members);
            let held = if twice {
                format!("{second}, {second}")
            } else {
                second
            };
            format!("{name}R0::A({held})")
        }
        Shape::AliasRing { members } => {
            let members = usize::from(members.get());
            for i in 0..members {
                writeln!(
                    defs,
                    "type {name}Q{i} = {name}A{i}({name}Q{}) | {name}N{i}({a_ty});",
                    (i + 1) % members
                )
                .unwrap();
            }
            writeln!(defs, "type {name} = {name}Q0;").unwrap();
            format!("{name}N0({a_val})")
        }
    }
}

/// A match on `value`, of the type `name` of `shape`, that gives `true`, if `shape` builds a
/// variant. Only the arm of the case that [`render_shape`] builds gives 1, so that a backend taking
/// another arm changes the program's result.
fn render_match(shape: Shape, name: &str, value: &str) -> Option<String> {
    let arms = match shape {
        Shape::Enum => "A(x) => 1, B(x) => 0, N => 0".to_string(),
        Shape::Ring { twice, .. } => {
            let held = if twice { "x, y" } else { "x" };
            format!("A({held}) => 1, N(x) => 0")
        }
        Shape::AliasRing { .. } => format!("{name}A0(x) => 0, {name}N0(x) => 1"),
        _ => return None,
    };
    Some(format!("(match {value} {{ {arms} }}) == 1"))
}

/// Compiles and runs `program`; panics on a finding.
pub fn check_deep_types(program: &DeepProgram) -> Report {
    let source = program.render();
    let report = check_source(&source);
    match &report {
        // The generator nests source a few levels only, far below the nesting limit: a program can
        // only be rejected by a compiler limit.
        Report::Rejected { category, message } => assert!(
            category == "CompilerLimitExceeded",
            "rejected for another reason than a limit ({category}): {message}\n{source}"
        ),
        Report::Ran { outcome, .. } => assert!(
            matches!(outcome, Outcome::Value { value: 1, .. } | Outcome::Limit),
            "computed {outcome:?} instead of 1:\n{source}"
        ),
    }
    report
}
