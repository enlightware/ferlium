// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Generator of webs of impls whose selection must not depend on the order of anything.
//!
//! A web is a few generic records, some of whose fields hold earlier records, a callback, which
//! has no `Serialize`, or the parameter. Each record may have a written `Serialize` impl, for all
//! its instantiations or for one that the program does not use, and an impl of `Conv`, a trait
//! with an output. Their prerequisites name other records of the web, so that impls require one
//! another in circles, some of them through `Conv`, or a trait without impls, so that a written
//! impl whose head matches does not apply. The program calls `serialize` and `conv` on some
//! records.
//!
//! The same web is rendered in several orders: of the impls, of the prerequisites of each impl,
//! of the fields as their names sort, and of the functions that make the calls. Which impl serves
//! each application, and whether it holds, must not depend on these orders: every rendering must
//! compile alike and compute the same value. Each written impl gives a marker of its own, which a
//! serialization's weight keeps wherever it sits, and the calls' results are combined by position,
//! so that a call served by another dictionary changes the value.

use arbitrary::{Result, Unstructured};
use std::fmt::Write;

/// A field of a record of the web.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WebField {
    /// The parameter `T`.
    Param,
    /// An earlier record of the web, at `T`.
    Earlier(usize),
    /// A callback, which has no `Serialize`.
    Callback,
}

/// A prerequisite of an impl of the web.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WebRequirement {
    /// `Serialize` of a record of the web.
    Serialize(usize),
    /// `Conv<Out = int>` of a record of the web: a circle through it may not close.
    Conv(usize),
    /// `T: Serialize`.
    ParamSerialize,
    /// `T: Missing`, a trait without impls.
    Missing,
}

/// How a record of the web is serialized.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WebSerialize {
    /// By derivation only.
    Derived,
    /// By a written impl for all its instantiations, with these prerequisites.
    Written(Vec<WebRequirement>),
    /// By a written impl for an instantiation that the program does not use.
    OtherInstance,
}

/// A record of the web and its impls.
#[derive(Clone, Debug)]
pub struct WebType {
    pub fields: Vec<WebField>,
    pub serialize: WebSerialize,
    /// The prerequisites of its impl of `Conv`, if it has one.
    pub conv: Option<Vec<WebRequirement>>,
}

/// A call of the program.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WebCall {
    Serialize(usize),
    Conv(usize),
}

/// A generated web.
#[derive(Clone, Debug)]
pub struct ImplWeb {
    pub types: Vec<WebType>,
    pub calls: Vec<WebCall>,
}

/// An order in which a web is rendered.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WebOrder {
    Written,
    Reversed,
    Rotated,
}

/// The orders of every web, the written one first.
pub const WEB_ORDERS: [WebOrder; 3] = [WebOrder::Written, WebOrder::Reversed, WebOrder::Rotated];

impl WebOrder {
    /// The order of this name, as a finding prints it in lower case.
    pub fn from_name(name: &str) -> Option<Self> {
        WEB_ORDERS
            .into_iter()
            .find(|order| format!("{order:?}").eq_ignore_ascii_case(name))
    }

    fn apply<T>(self, mut items: Vec<T>) -> Vec<T> {
        match self {
            Self::Written => {}
            Self::Reversed => items.reverse(),
            Self::Rotated if !items.is_empty() => items.rotate_left(1),
            Self::Rotated => {}
        }
        items
    }

    /// The position of the item at `index` among `count`, as [`Self::apply`] places it.
    fn position(self, index: usize, count: usize) -> usize {
        match self {
            Self::Written => index,
            Self::Reversed => count - 1 - index,
            Self::Rotated => (index + count - 1) % count,
        }
    }
}

impl ImplWeb {
    pub fn generate(u: &mut Unstructured) -> Result<Self> {
        let count = u.int_in_range(2..=4)?;
        let mut types = Vec::with_capacity(count);
        for index in 0..count {
            let mut fields = Vec::new();
            for _ in 0..u.int_in_range(1..=3)? {
                fields.push(match u.int_in_range(0..=5)? {
                    2..=4 if index > 0 => WebField::Earlier(u.int_in_range(0..=index - 1)?),
                    5 => WebField::Callback,
                    _ => WebField::Param,
                });
            }
            // The parameter is used, so that the record is generic.
            if fields.iter().all(|field| *field == WebField::Callback) {
                fields[0] = WebField::Param;
            }
            types.push(WebType {
                fields,
                serialize: WebSerialize::Derived,
                conv: None,
            });
        }
        // The impls come after all records, as their prerequisites name any of them.
        for ty in &mut types {
            ty.serialize = match u.int_in_range(0..=4)? {
                0 | 1 => WebSerialize::Derived,
                2 | 3 => WebSerialize::Written(requirements(u, count)?),
                _ => WebSerialize::OtherInstance,
            };
            if u.arbitrary()? {
                ty.conv = Some(requirements(u, count)?);
            }
        }
        let mut calls = Vec::new();
        for _ in 0..u.int_in_range(1..=4)? {
            let index = u.choose_index(count)?;
            calls.push(if types[index].conv.is_some() && u.arbitrary()? {
                WebCall::Conv(index)
            } else {
                WebCall::Serialize(index)
            });
        }
        Ok(Self { types, calls })
    }

    pub fn render(&self, order: WebOrder) -> String {
        let mut out = String::new();
        out.push_str("trait Missing<Self> { fn missing(x: Self) -> int; }\n");
        out.push_str("trait Conv<Self |-> Out> { fn conv(x: Self) -> Out; }\n");
        out.push_str("fn cb() -> int { 0 }\n");
        // The weight of a record does not depend on the names of its fields, which the orders
        // change. It is 1 modulo 3 at any depth, and a written impl's marker 2, so that a derived
        // record never weighs as a written impl does.
        out.push_str(
            "fn weigh(d: DataValue) -> int {\n\tmatch d {\n\t\tDataValue::Int(n) => n,\n\t\tDataValue::Record(entries) => {\n\t\t\tlet mut t = 1;\n\t\t\tfor entry in entries {\n\t\t\t\tt = t + 3 * weigh(entry.1)\n\t\t\t};\n\t\t\tt\n\t\t},\n\t\t_ => 7,\n\t}\n}\n",
        );
        for (index, ty) in self.types.iter().enumerate() {
            let count = ty.fields.len();
            let fields: Vec<_> = ty
                .fields
                .iter()
                .enumerate()
                .map(|(field, kind)| {
                    let ty = match kind {
                        WebField::Param => "T".to_string(),
                        WebField::Earlier(earlier) => format!("K{earlier}<T>"),
                        WebField::Callback => "() -> int".to_string(),
                    };
                    format!("f{}: {ty}", order.position(field, count))
                })
                .collect();
            writeln!(out, "struct K{index}<T> {{ {} }}", fields.join(", ")).unwrap();
        }

        let mut impls = Vec::new();
        for (index, ty) in self.types.iter().enumerate() {
            match &ty.serialize {
                WebSerialize::Derived => {}
                WebSerialize::Written(requirements) => impls.push(format!(
                    "impl<T> Serialize for K{index}<T>{} {{\n\tfn serialize(x: K{index}<T>) -> DataValue {{ serialize({}) }}\n}}\n",
                    where_clause(requirements, order),
                    3002 + 3 * index,
                )),
                WebSerialize::OtherInstance => impls.push(format!(
                    "impl Serialize for K{index}<bool> {{\n\tfn serialize(x: K{index}<bool>) -> DataValue {{ serialize({}) }}\n}}\n",
                    6002 + 3 * index,
                )),
            }
            if let Some(requirements) = &ty.conv {
                impls.push(format!(
                    "impl<T> Conv for <Self = K{index}<T> |-> Out = int>{} {{\n\tfn conv(x: K{index}<T>) -> int {{ {} }}\n}}\n",
                    where_clause(requirements, order),
                    100 + index,
                ));
            }
        }
        for implementation in order.apply(impls) {
            out.push_str(&implementation);
        }

        // Each call is in a function of its own, compiled in the order of their definitions.
        let functions: Vec<_> = self
            .calls
            .iter()
            .enumerate()
            .map(|(index, call)| {
                let body = match call {
                    WebCall::Serialize(ty) => {
                        format!("weigh(serialize({}))", self.value(*ty, order))
                    }
                    WebCall::Conv(ty) => format!("conv({})", self.value(*ty, order)),
                };
                format!("fn t{index}() -> int {{ {body} }}\n")
            })
            .collect();
        for function in order.apply(functions) {
            out.push_str(&function);
        }
        let mut entry = "0".to_string();
        for index in 0..self.calls.len() {
            entry = format!("({entry}) * 31 + t{index}()");
        }
        out.push_str(&entry);
        out.push('\n');
        out
    }

    /// A value of the record `index` at `int`.
    fn value(&self, index: usize, order: WebOrder) -> String {
        let fields = &self.types[index].fields;
        let values: Vec<_> = fields
            .iter()
            .enumerate()
            .map(|(field, kind)| {
                let value = match kind {
                    WebField::Param => "1".to_string(),
                    WebField::Earlier(earlier) => self.value(*earlier, order),
                    WebField::Callback => "cb".to_string(),
                };
                format!("f{}: {value}", order.position(field, fields.len()))
            })
            .collect();
        format!("K{index} {{ {} }}", values.join(", "))
    }
}

fn requirements(u: &mut Unstructured, count: usize) -> Result<Vec<WebRequirement>> {
    let mut requirements = Vec::new();
    for _ in 0..u.int_in_range(0..=3)? {
        let requirement = match u.int_in_range(0..=9)? {
            0..=3 => WebRequirement::Serialize(u.choose_index(count)?),
            4..=6 => WebRequirement::Conv(u.choose_index(count)?),
            7 | 8 => WebRequirement::ParamSerialize,
            _ => WebRequirement::Missing,
        };
        if !requirements.contains(&requirement) {
            requirements.push(requirement);
        }
    }
    Ok(requirements)
}

fn where_clause(requirements: &[WebRequirement], order: WebOrder) -> String {
    if requirements.is_empty() {
        return String::new();
    }
    let clauses: Vec<_> = requirements
        .iter()
        .map(|requirement| match requirement {
            WebRequirement::Serialize(index) => format!("K{index}<T>: Serialize"),
            WebRequirement::Conv(index) => format!("K{index}<T>: Conv<Out = int>"),
            WebRequirement::ParamSerialize => "T: Serialize".to_string(),
            WebRequirement::Missing => "T: Missing".to_string(),
        })
        .collect();
    format!("\nwhere\n\t{}\n", order.apply(clauses).join(",\n\t"))
}
