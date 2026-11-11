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
//! - concrete impls fixing `E` to `()`, `fallible` or all effects, blanket impls over a wrapper forwarding,
//!   extending or constraining the evidence's `E` (possibly of another trait), and impls for a
//!   callback carrier whose `E` comes from the stored callable;
//! - generic callers reaching the methods directly, through declared signatures, method
//!   references, eager and lazy std adaptors, joins of callables, closures built in loops, and
//!   other callers;
//! - declared callers fixing the trait's effect by one or two `where` bounds on the same
//!   application, which combine by polarity, possibly calling another such caller whose bounds
//!   their own must fit;
//! - traits whose default method reaches a method through such bounds on `Self`, implemented by
//!   their default for concrete types;
//! - a wrapper with a custom `Value` impl whose methods call a method that a prerequisite
//!   requires to be pure, used through containers, derivation and generic functions;
//! - an entry expression summing calls on concrete values, with callbacks that are pure, fail,
//!   read or write.
//!
//! `effects::write()` counts and `effects::read()` returns the count, so the result of a program
//! depends on which effects ran and in which order. Every program computes an `int`, so outcomes
//! compare as plain values or failure kinds.

use arbitrary::{Result, Unstructured};
use ferlium::types::effects::{
    EffType, Effect, EffectRow, PrimitiveEffect, effect, effect_read, effect_write, no_effects,
};
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

fn fallible() -> EffType {
    effect(PrimitiveEffect::Fallible)
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
    pub concrete: [Option<(EffType, u8)>; 2],
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

const CALLBACK_SHAPES: u8 = 8;

impl Callback {
    fn eff(self) -> EffType {
        match self.shape {
            0..=2 => no_effects(),
            3 | 4 => fallible(),
            5 => effect_read(),
            6 => effect_write(),
            _ => effect_write().union(&fallible()),
        }
    }

    fn render(self, var: &str) -> String {
        let c = self.constant;
        match self.shape {
            0 => format!("|{var}| {var} + {c}"),
            1 => format!("|{var}| {var} * {c}"),
            2 => format!("|{var}| {c}"),
            3 => format!("|{var}| idiv({c}, {var})"),
            4 => format!("|{var}| idiv({var}, {c})"),
            5 => format!("|{var}| {var} + effects::read()"),
            6 => format!("|{var}| {{ effects::write(); {var} + {c} }}"),
            _ => format!("|{var}| {{ effects::write(); idiv({c}, {var}) }}"),
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
    /// Calls a callable chosen between two by a condition.
    Join,
    /// Calls a closure built in each iteration of a loop.
    LoopClosure,
    /// Calls an earlier caller on `W(s)`.
    Delegate(usize),
    /// A declared signature fixing `E` by one or two bounds on the same application,
    /// `fn g<T>(s: T, x: int, f: (int) -> int ! R) -> int where T: Tr<! E = B0>, T: Tr<! E = B1>`,
    /// each row being `()` or `(fallible)`.
    Bounded(Bounds),
}

/// The written rows of a bounded caller, each `fallible` when true, else `()`.
#[derive(Clone, Copy, Debug)]
pub struct Bounds {
    pub first: bool,
    pub second: Option<bool>,
    /// The row of the callback parameter, for traits taking a callback.
    pub callback: bool,
    /// An earlier bounded caller of the same trait to call instead of the method.
    pub via: Option<usize>,
}

fn fixed_row(is_fallible: bool) -> &'static str {
    if is_fallible { "(fallible)" } else { "()" }
}

fn fixed_eff(is_fallible: bool) -> EffType {
    if is_fallible {
        fallible()
    } else {
        no_effects()
    }
}

impl Bounds {
    /// Whether the evidence the bounds combine into is `fallible`: performed bounds intersect,
    /// received ones unite, invariant ones must be equal (`None` if they differ).
    fn combined(&self, kind: TraitKind) -> Option<bool> {
        let second = self.second.unwrap_or(self.first);
        match kind {
            _ if kind.positive() => Some(self.first && second),
            TraitKind::Callback => Some(self.first || second),
            _ => (self.first == second).then_some(self.first),
        }
    }

    /// Whether an impl with effect `eff` fits the bounds; only used to steer generation.
    fn fit(&self, kind: TraitKind, eff: &EffType) -> bool {
        let Some(combined) = self.combined(kind) else {
            return false;
        };
        let bound = fixed_eff(combined);
        match kind {
            _ if kind.positive() => eff.is_subset_of(&bound),
            TraitKind::Callback => bound.is_subset_of(eff),
            _ => *eff == bound,
        }
    }
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

/// A trait `D<j>` whose default method reaches a method of `kind` through bounds on `Self`.
#[derive(Clone, Debug)]
pub struct DefaultTrait {
    pub kind: TraitKind,
    /// The bounds on `Self`, the row of the callback parameter, and a bounded caller to call
    /// instead of the method.
    pub bounds: Bounds,
    /// Whether the default method declares `fallible` whatever it performs.
    pub widened: bool,
    /// The values whose types implement the trait by its default.
    pub impls: Vec<SelfValue>,
    /// The entry terms calling the default method: an impl, `x` and a callback.
    pub terms: Vec<(usize, i8, Option<Callback>)>,
}

/// How a use of the `Value` wrapper reaches its value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Through {
    /// In the entry expression.
    Inline,
    /// Through a function without annotations.
    Inferred,
    /// Through a function declaring the prerequisite of the wrapper's impl.
    Declared,
    /// Through a function generic over the effect of a carrier's callback, which never fits.
    Generic,
}

/// A use of the `Value` wrapper `V<T>`.
#[derive(Clone, Debug)]
pub struct ValueUse {
    pub value: SelfValue,
    /// What holds the wrapper: nothing, a tuple, an array, a struct or an option.
    pub container: u8,
    /// Comparing, printing, copying, or only dropping.
    pub operation: u8,
    pub through: Through,
}

/// A wrapper `V<T>` with a custom `Value` impl whose methods call a method of `kind`, which a
/// prerequisite requires to be pure.
#[derive(Clone, Debug)]
pub struct ValueWrapper {
    pub kind: TraitKind,
    pub uses: Vec<ValueUse>,
}

/// A generated program.
#[derive(Clone, Debug)]
pub struct EffectProgram {
    pub traits: Vec<TraitImpls>,
    pub callers: Vec<Caller>,
    pub terms: Vec<Term>,
    pub cycles: Vec<Cycle>,
    pub defaults: Vec<DefaultTrait>,
    pub value_wrapper: Option<ValueWrapper>,
}

/// One of the two callback parameters, `f0` and `f1`, of a function of a recursive cycle.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CallbackParam {
    F0,
    F1,
}

const CALLBACK_PARAMS: [CallbackParam; 2] = [CallbackParam::F0, CallbackParam::F1];

impl CallbackParam {
    fn index(self) -> usize {
        self as usize
    }
}

/// An argument that a function of a recursive cycle passes for a callback parameter.
#[derive(Clone, Copy, Debug)]
pub enum CycleArg {
    /// One of the caller's own callback parameters.
    Param(CallbackParam),
    Closure(Callback),
}

/// A function of a recursive cycle, calling the next one with a decreasing counter.
#[derive(Clone, Debug)]
pub struct CycleFn {
    /// Whether the function writes its effect generics and the types of its parameters.
    pub annotated: bool,
    /// Whether the written row of each parameter also declares `fallible`.
    pub declares_fallible: [bool; 2],
    /// The arguments of each call to the next function.
    pub calls: Vec<[CycleArg; 2]>,
    /// The callback parameter called when the counter ends, if any.
    pub performs: Option<CallbackParam>,
}

/// Functions that call each other in a cycle, each possibly writing its own effect generics.
#[derive(Clone, Debug)]
pub struct Cycle {
    pub functions: Vec<CycleFn>,
    pub arguments: [Callback; 2],
    pub count: u8,
}

/// Rendering choices that must not change a program's outcome.
#[derive(Clone, Copy, Debug, Default)]
pub struct Variant {
    /// Effect variables named `Q` instead of `E`.
    pub rename: bool,
    /// Impls, the bounds of bounded callers, and the compilation of entry terms, in reverse
    /// order.
    pub reverse: bool,
}

fn arbitrary_cycle(u: &mut Unstructured) -> Result<Cycle> {
    let length = u.int_in_range(1..=3)?;
    let mut functions = Vec::new();
    for _ in 0..length {
        let call_count = u.int_in_range(1..=2)?;
        let mut calls = Vec::new();
        for _ in 0..call_count {
            let mut arguments = CALLBACK_PARAMS.map(CycleArg::Param);
            for argument in &mut arguments {
                *argument = match u.int_in_range(0..=3)? {
                    0 => CycleArg::Closure(arbitrary_callback(u)?),
                    1 => CycleArg::Param(CallbackParam::F0),
                    2 => CycleArg::Param(CallbackParam::F1),
                    _ => *argument,
                };
            }
            calls.push(arguments);
        }
        functions.push(CycleFn {
            annotated: u.ratio(3, 4)?,
            declares_fallible: [u.ratio(1, 4)?, u.ratio(1, 4)?],
            calls,
            performs: match u.int_in_range(0..=2)? {
                0 => None,
                1 => Some(CallbackParam::F0),
                _ => Some(CallbackParam::F1),
            },
        });
    }
    Ok(Cycle {
        functions,
        arguments: [arbitrary_callback(u)?, arbitrary_callback(u)?],
        count: u.int_in_range(0..=3)?,
    })
}

impl Cycle {
    fn render_function(&self, cycle: usize, index: usize, e: &str) -> String {
        let function = &self.functions[index];
        let next = (index + 1) % self.functions.len();
        let header = if function.annotated {
            let row = |param: CallbackParam| {
                let param = param.index();
                if function.declares_fallible[param] {
                    format!("(fallible, {e}{param})")
                } else {
                    format!("{e}{param}")
                }
            };
            format!(
                "fn r{cycle}_{index}<! {e}0, {e}1>(f0: (int) -> int ! {}, f1: (int) -> int ! {}, n: int) -> int",
                row(CallbackParam::F0),
                row(CallbackParam::F1)
            )
        } else {
            format!("fn r{cycle}_{index}(f0, f1, n: int) -> int")
        };
        let calls: Vec<_> = function
            .calls
            .iter()
            .map(|arguments| {
                let render = |argument: &CycleArg| match argument {
                    CycleArg::Param(param) => format!("f{}", param.index()),
                    CycleArg::Closure(callback) => callback.render("z"),
                };
                format!(
                    "r{cycle}_{next}({}, {}, n - 1)",
                    render(&arguments[0]),
                    render(&arguments[1])
                )
            })
            .collect();
        let base = match function.performs {
            Some(param) => format!("f{}(n)", param.index()),
            None => "0".to_string(),
        };
        format!(
            "{header} {{\n\tif n > 0 {{\n\t\t{}\n\t}} else {{\n\t\t{base}\n\t}}\n}}\n",
            calls.join(" + ")
        )
    }

    fn render_term(&self, cycle: usize) -> String {
        format!(
            "r{cycle}_0({}, {}, {})",
            self.arguments[0].render("z"),
            self.arguments[1].render("z"),
            self.count
        )
    }
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
                    let eff = match u.int_in_range(0..=2)? {
                        0 => no_effects(),
                        1 => fallible(),
                        _ => EffType::all_primitives(),
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
                concrete: [Some((fallible(), 0)), Some((no_effects(), 0))],
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
            cycles: Vec::new(),
            defaults: Vec::new(),
            value_wrapper: None,
        };

        let caller_count = u.int_in_range(0..=4)?;
        for _ in 0..caller_count {
            let flavor = match u.int_in_range(0..=11)? {
                0 => Flavor::Direct,
                1 => Flavor::Declared,
                2 => Flavor::Reference,
                3 => Flavor::EagerMap,
                4 => Flavor::EagerFilter,
                5 => Flavor::LazyMap,
                6 => Flavor::LazyFold,
                7 => Flavor::Join,
                8 => Flavor::LoopClosure,
                9 | 10 => Flavor::Bounded(Bounds {
                    first: u.arbitrary()?,
                    second: if u.arbitrary()? {
                        Some(u.arbitrary()?)
                    } else {
                        None
                    },
                    callback: u.arbitrary()?,
                    via: None,
                }),
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
                    let mut kind = u.choose(&program.traits)?.kind;
                    // A bounded caller mostly calls an earlier one of the same trait.
                    let bounded_kinds: Vec<_> = program
                        .callers
                        .iter()
                        .filter(|callee| matches!(callee.flavor, Flavor::Bounded(_)))
                        .map(|callee| callee.kind)
                        .collect();
                    if matches!(flavor, Flavor::Bounded(_))
                        && !bounded_kinds.is_empty()
                        && u.ratio(3, 4)?
                    {
                        kind = *u.choose(&bounded_kinds)?;
                    }
                    // A declared signature names the trait's effect in a callback-free form only.
                    let flavor = match flavor {
                        Flavor::Declared if !matches!(kind, TraitKind::Own | TraitKind::Both) => {
                            Flavor::Direct
                        }
                        Flavor::Bounded(mut bounds) => {
                            let callees: Vec<_> = (0..program.callers.len())
                                .filter(|index| {
                                    let callee = &program.callers[*index];
                                    callee.kind == kind
                                        && matches!(callee.flavor, Flavor::Bounded(_))
                                })
                                .collect();
                            if !callees.is_empty() && u.ratio(3, 4)? {
                                let callee = *u.choose(&callees)?;
                                bounds.via = Some(callee);
                                // Equal bounds always fit the callee's; others may not.
                                if u.arbitrary()?
                                    && let Flavor::Bounded(callee_bounds) =
                                        program.callers[callee].flavor
                                {
                                    bounds.first = callee_bounds.first;
                                    bounds.second = callee_bounds.second;
                                    bounds.callback = callee_bounds.callback;
                                }
                            }
                            // Mostly, the callback row fits the evidence the bounds combine into.
                            if kind.takes_callback()
                                && u.ratio(3, 4)?
                                && let Some(combined) = bounds.combined(kind)
                            {
                                bounds.callback = combined;
                            }
                            Flavor::Bounded(bounds)
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
                                | Flavor::LoopClosure
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
        let cycle_count = u.int_in_range(0..=2)?;
        for _ in 0..cycle_count {
            program.cycles.push(arbitrary_cycle(u)?);
        }
        // Later constructs are chosen last, so that earlier inputs keep their programs.
        let default_count = u.int_in_range(0..=2)?;
        for _ in 0..default_count {
            if let Some(default) = program.default_trait(u)? {
                program.defaults.push(default);
            }
        }
        // An exhausted input answers yes to `ratio`: ask for the absence of the wrapper.
        if !u.ratio(2, 3)? {
            program.value_wrapper = program.arbitrary_value_wrapper(u)?;
        }
        Ok(program)
    }

    /// Whether the program must be compiled as trusted code, as it implements `Value`.
    pub fn needs_trust(&self) -> bool {
        self.value_wrapper.is_some()
    }

    /// The bounded callers of the trait `kind`.
    fn bounded_callers(&self, kind: TraitKind) -> Vec<usize> {
        (0..self.callers.len())
            .filter(|index| {
                let callee = &self.callers[*index];
                callee.kind == kind && matches!(callee.flavor, Flavor::Bounded(_))
            })
            .collect()
    }

    /// Whether a function with these bounds may fail, calling the method or its `via` callee.
    fn bounded_may_fail(&self, kind: TraitKind, bounds: &Bounds) -> bool {
        if let Some(callee) = bounds.via
            && let Flavor::Bounded(callee_bounds) = self.callers[callee].flavor
        {
            return self.bounded_may_fail(kind, &callee_bounds);
        }
        match kind {
            TraitKind::OwnFallible => true,
            TraitKind::Callback => false,
            _ => bounds.combined(kind).unwrap_or(true),
        }
    }

    fn default_trait(&self, u: &mut Unstructured) -> Result<Option<DefaultTrait>> {
        let kind = u.choose(&self.traits)?.kind;
        let mut bounds = Bounds {
            first: u.arbitrary()?,
            second: if u.arbitrary()? {
                Some(u.arbitrary()?)
            } else {
                None
            },
            callback: u.arbitrary()?,
            via: None,
        };
        let callees = self.bounded_callers(kind);
        if !callees.is_empty() && u.ratio(1, 2)? {
            let callee = *u.choose(&callees)?;
            bounds.via = Some(callee);
            // Equal bounds always fit the callee's; others may not.
            if u.ratio(3, 4)?
                && let Flavor::Bounded(callee_bounds) = self.callers[callee].flavor
            {
                bounds.first = callee_bounds.first;
                bounds.second = callee_bounds.second;
                bounds.callback = callee_bounds.callback;
            }
        }
        if kind.takes_callback()
            && u.ratio(3, 4)?
            && let Some(combined) = bounds.combined(kind)
        {
            bounds.callback = combined;
        }
        // Mostly, the types implementing the trait fit its bounds; the others must be rejected.
        let fitting = u.ratio(7, 8)?;
        let mut impls: Vec<SelfValue> = Vec::new();
        for _ in 0..u.int_in_range(1..=4)? {
            let value = self.plain_self_value(u, 2)?;
            let Some(eff) = self.eff(kind, &value) else {
                continue;
            };
            if fitting && !bounds.fit(kind, &eff) {
                continue;
            }
            let ty = render_type(&value);
            if impls.iter().all(|other| render_type(other) != ty) {
                impls.push(value);
            }
        }
        if impls.is_empty() {
            return Ok(None);
        }
        let mut terms = Vec::new();
        for _ in 0..u.int_in_range(0..=2)? {
            let callback = if kind.takes_callback() {
                let callback = arbitrary_callback(u)?;
                // Mostly, the callback fits the row the default method declares for it.
                if !callback.eff().is_subset_of(&fixed_eff(bounds.callback)) && u.ratio(7, 8)? {
                    continue;
                }
                Some(callback)
            } else {
                None
            };
            terms.push((
                u.int_in_range(0..=impls.len() - 1)?,
                u.int_in_range(-1..=3)?,
                callback,
            ));
        }
        Ok(Some(DefaultTrait {
            kind,
            bounds,
            widened: u.ratio(1, 8)?,
            impls,
            terms,
        }))
    }

    fn arbitrary_value_wrapper(&self, u: &mut Unstructured) -> Result<Option<ValueWrapper>> {
        // The prerequisite fixes the effect to `()`, which `OwnFallible` always exceeds.
        let kinds: Vec<_> = self
            .traits
            .iter()
            .map(|implementation| implementation.kind)
            .filter(|kind| *kind != TraitKind::OwnFallible)
            .collect();
        if kinds.is_empty() {
            return Ok(None);
        }
        let kind = *u.choose(&kinds)?;
        let carrier = self
            .implementation(kind)
            .is_some_and(|implementation| implementation.carrier);
        let mut uses = Vec::new();
        for _ in 0..u.int_in_range(1..=3)? {
            let through = match u.int_in_range(0..=8)? {
                0..=2 => Through::Inline,
                3..=5 => Through::Inferred,
                6 | 7 => Through::Declared,
                _ if carrier => Through::Generic,
                _ => Through::Inferred,
            };
            // Mostly, the value fits the prerequisite; the others must be rejected.
            let fitting = u.ratio(5, 6)?;
            for _ in 0..4 {
                let value = if through == Through::Generic {
                    SelfValue::C(arbitrary_callback(u)?)
                } else {
                    self.self_value(u, 2)?
                };
                let Some(eff) = self.eff(kind, &value) else {
                    continue;
                };
                // An impl accepting more callbacks than pure ones still accepts those.
                let fits = kind == TraitKind::Callback || eff.is_empty();
                if fitting && !fits && through != Through::Generic {
                    continue;
                }
                uses.push(ValueUse {
                    value,
                    container: u.int_in_range(0..=4)?,
                    operation: u.int_in_range(0..=3)?,
                    through,
                });
                break;
            }
        }
        Ok(Some(ValueWrapper { kind, uses }))
    }

    /// A self value without callback carrier, so that its type can be an impl's input.
    fn plain_self_value(&self, u: &mut Unstructured, depth: usize) -> Result<SelfValue> {
        Ok(match u.int_in_range(0..=2)? {
            2 if depth > 0 => SelfValue::W(Box::new(self.plain_self_value(u, depth - 1)?)),
            index => SelfValue::S(index & 1, u.int_in_range(0..=2)?),
        })
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
        // Mostly, a bounded caller gets values and callbacks that fit its bounds.
        let bounds = match caller.map(|index| self.callers[index].flavor) {
            Some(Flavor::Bounded(bounds)) if u.ratio(3, 4)? => Some(bounds),
            _ => None,
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
            if bounds.is_some_and(|bounds| !bounds.fit(kind, &eff)) {
                continue;
            }
            let callback = if kind.takes_callback() {
                let callback = arbitrary_callback(u)?;
                // A callback must perform no more than the `E` of the impl it reaches.
                if !callback.eff().is_subset_of(&eff)
                    || bounds.is_some_and(|bounds| {
                        !callback.eff().is_subset_of(&fixed_eff(bounds.callback))
                    })
                {
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
    fn eff(&self, kind: TraitKind, value: &SelfValue) -> Option<EffType> {
        let implementation = self.implementation(kind)?;
        match value {
            SelfValue::S(index, _) => implementation.concrete[*index]
                .as_ref()
                .map(|(eff, _)| eff.clone()),
            SelfValue::C(callback) => implementation.carrier.then(|| callback.eff()),
            SelfValue::W(inner) => match implementation.wrap? {
                WrapImpl::Forward {
                    inner: inner_kind, ..
                } => self.eff(inner_kind, inner),
                WrapImpl::Extend => self.eff(kind, inner).map(|eff| eff.union(&fallible())),
                WrapImpl::Pure => self.eff(kind, inner)?.is_empty().then(no_effects),
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
        if self.value_wrapper.is_some() {
            out.push_str("struct V<T>(T)\nstruct N<T> { member: T }\n");
            out.push_str("fn same(a, b) {\n\tif a == b {\n\t\t1\n\t} else {\n\t\t0\n\t}\n}\n");
        }

        let mut impls = Vec::new();
        for implementation in &self.traits {
            render_impls(implementation, e, &mut impls);
        }
        if let Some(wrapper) = &self.value_wrapper {
            impls.push(render_value_impl(wrapper.kind, e));
        }
        if variant.reverse {
            impls.reverse();
        }
        for implementation in impls {
            out.push_str(&implementation);
        }

        for (index, caller) in self.callers.iter().enumerate() {
            out.push_str(&self.render_caller(index, caller, e, variant.reverse));
        }

        // A default method may call a bounded caller, so its trait comes after the callers.
        let mut default_impls = Vec::new();
        for (index, default) in self.defaults.iter().enumerate() {
            out.push_str(&self.render_default_trait(index, default, e, variant.reverse));
            for value in &default.impls {
                default_impls.push(format!("impl D{index} for {} {{}}\n", render_type(value)));
            }
        }
        if variant.reverse {
            default_impls.reverse();
        }
        for implementation in default_impls {
            out.push_str(&implementation);
        }
        if let Some(wrapper) = &self.value_wrapper {
            for (index, value_use) in wrapper.uses.iter().enumerate() {
                out.push_str(&value_use.render_function(index, wrapper.kind, e));
            }
        }

        let mut cycle_functions = Vec::new();
        for (index, cycle) in self.cycles.iter().enumerate() {
            for function in 0..cycle.functions.len() {
                cycle_functions.push(cycle.render_function(index, function, e));
            }
        }
        if variant.reverse {
            cycle_functions.reverse();
        }
        for function in cycle_functions {
            out.push_str(&function);
        }

        let mut terms: Vec<_> = self
            .terms
            .iter()
            .map(|term| self.render_term(term))
            .collect();
        terms.extend(
            self.cycles
                .iter()
                .enumerate()
                .map(|(index, cycle)| cycle.render_term(index)),
        );
        for (index, default) in self.defaults.iter().enumerate() {
            for (implementation, x, callback) in &default.terms {
                let mut args = vec![render_value(&default.impls[*implementation]), x.to_string()];
                args.extend(callback.map(|callback| callback.render("z")));
                terms.push(format!("d{index}({})", args.join(", ")));
            }
        }
        if let Some(wrapper) = &self.value_wrapper {
            terms.extend(
                wrapper
                    .uses
                    .iter()
                    .enumerate()
                    .map(|(index, value_use)| value_use.render_term(index)),
            );
        }
        if terms.is_empty() {
            out.push_str("0\n");
        } else if variant.reverse {
            // The terms are compiled in reverse order but still evaluated in order, as their
            // effects are observable.
            out.push_str("{\n");
            for (index, term) in terms.iter().enumerate().rev() {
                writeln!(out, "\tlet k{index} = || {term};").unwrap();
            }
            let calls: Vec<_> = (0..terms.len())
                .map(|index| format!("k{index}()"))
                .collect();
            writeln!(out, "\t{}\n}}", calls.join(" + ")).unwrap();
        } else {
            out.push_str(&terms.join(" + "));
            out.push('\n');
        }
        out
    }

    fn render_caller(&self, index: usize, caller: &Caller, e: &str, reverse: bool) -> String {
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
            Flavor::Join => {
                if kind.takes_callback() {
                    format!(
                        "fn g{index}(s, x, f) {{\n\tlet h = if x > 0 {{ f }} else {{ |y| y + 1 }};\n\t{}\n}}\n",
                        method_call(kind, "s", "x", "h")
                    )
                } else {
                    format!(
                        "fn g{index}(s, x) {{\n\tlet h = if x > 0 {{ |y| {} }} else {{ |y| y }};\n\th(x)\n}}\n",
                        call("s", "y")
                    )
                }
            }
            Flavor::LoopClosure => format!(
                "fn g{index}(s, x{f_param}{a_param}) {{\n\tlet mut t = x;\n\tfor y in a {{\n\t\tlet h = |z| {};\n\t\tt = t + h(y)\n\t}};\n\tt\n}}\n",
                call("s", "z")
            ),
            Flavor::Bounded(bounds) => {
                let (f_param, clauses, body) = bounded_parts(kind, &bounds, "T", e, reverse);
                format!(
                    "fn g{index}<T>(s: T, x: int{f_param}) -> int\nwhere\n{clauses}\n{{\n\t{body}\n}}\n"
                )
            }
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

    fn render_default_trait(
        &self,
        index: usize,
        default: &DefaultTrait,
        e: &str,
        reverse: bool,
    ) -> String {
        let kind = default.kind;
        let (f_param, clauses, body) = bounded_parts(kind, &default.bounds, "Self", e, reverse);
        let row = if default.widened || self.bounded_may_fail(kind, &default.bounds) {
            " ! fallible"
        } else {
            ""
        };
        format!(
            "trait D{index}<Self>\nwhere\n{clauses}\n{{\n\tfn d{index}(s: Self, x: int{f_param}) -> int{row} {{\n\t\t{body}\n\t}}\n}}\n"
        )
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

/// The callback parameter, `where` clauses and body of a function reaching a method of `kind`
/// through fixed bounds on `subject`.
fn bounded_parts(
    kind: TraitKind,
    bounds: &Bounds,
    subject: &str,
    e: &str,
    reverse: bool,
) -> (String, String, String) {
    let i = kind.index();
    let f_param = if kind.takes_callback() {
        format!(", f: (int) -> int ! {}", fixed_row(bounds.callback))
    } else {
        String::new()
    };
    let mut clauses = vec![format!(
        "\t{subject}: Tr{i}<! {e} = {}>",
        fixed_row(bounds.first)
    )];
    if let Some(second) = bounds.second {
        clauses.push(format!("\t{subject}: Tr{i}<! {e} = {}>", fixed_row(second)));
    }
    // Bounds combine whatever their order.
    if reverse {
        clauses.reverse();
    }
    let body = match bounds.via {
        Some(callee) => {
            let f_arg = if kind.takes_callback() { ", f" } else { "" };
            format!("g{callee}(s, x{f_arg})")
        }
        None => method_call(kind, "s", "x", "f"),
    };
    (f_param, clauses.join(",\n"), body)
}

impl ValueUse {
    /// The use of the wrapper around the value `s`.
    fn body(&self, s: &str) -> String {
        let made = match self.container {
            0 => format!("V({s})"),
            1 => format!("(V({s}), 1)"),
            2 => format!("[V({s})]"),
            3 => format!("N {{ member: V({s}) }}"),
            _ => format!("Some(V({s}))"),
        };
        let used = match self.operation {
            0 => "same(v, v)",
            1 => "len(to_string(v))",
            2 => "let w = [v, v];\n\tsame(w, w)",
            _ => "1",
        };
        format!("let v = {made};\n\t{used}")
    }

    fn render_function(&self, index: usize, kind: TraitKind, e: &str) -> String {
        let i = kind.index();
        match self.through {
            Through::Inline => String::new(),
            Through::Inferred => format!("fn u{index}(s) {{\n\t{}\n}}\n", self.body("s")),
            Through::Declared => format!(
                "fn u{index}<T>(s: T) -> int\nwhere\n\tT: Value,\n\tT: Tr{i}<! {e} = ()>\n{{\n\t{}\n}}\n",
                self.body("s")
            ),
            Through::Generic => format!(
                "fn u{index}<! {e}>(f: (int) -> int ! {e}) -> int {{\n\t{}\n}}\n",
                self.body("C { f: f }")
            ),
        }
    }

    fn render_term(&self, index: usize) -> String {
        match (&self.through, &self.value) {
            (Through::Inline, value) => format!("{{\n\t{}\n}}", self.body(&render_value(value))),
            (Through::Generic, SelfValue::C(callback)) => {
                format!("u{index}({})", callback.render("w"))
            }
            (_, value) => format!("u{index}({})", render_value(value)),
        }
    }
}

/// The custom `Value` impl of the wrapper `V<T>`, whose methods call a method of `kind`.
fn render_value_impl(kind: TraitKind, e: &str) -> String {
    let i = kind.index();
    let probe = |x: &str| match kind {
        TraitKind::Returned => format!("{{ let h = m{i}({x}.0); h(0) }}"),
        _ => method_call(kind, &format!("{x}.0"), "0", "|z| z + 1"),
    };
    format!(
        "impl<T> Value for V<T>\nwhere\n\tT: Value,\n\tT: Tr{i}<! {e} = ()>\n{{\n\tfn eq(x: V<T>, y: V<T>) -> bool {{ {} == {} }}\n\tfn to_string(x: V<T>) -> string {{ to_string({}) }}\n\tfn hash(x: V<T>, state: &mut hasher) {{ hash({}, state) }}\n\tfn clone(x: V<T>) -> V<T> {{ V(x.0) }}\n\tfn drop(x: &mut V<T>) {{}}\n}}\n",
        probe("x"),
        probe("y"),
        probe("x"),
        probe("x"),
    )
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

/// The type of a value without callback carrier.
fn render_type(value: &SelfValue) -> String {
    match value {
        SelfValue::S(index, _) => format!("S{index}"),
        SelfValue::W(inner) => format!("W<{}>", render_type(inner)),
        SelfValue::C(_) => unreachable!("a carrier's type has an effect"),
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
        let Some((eff, variant)) = concrete else {
            continue;
        };
        let row = EffectRow(eff);
        let body = concrete_body(kind, eff, *variant);
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

fn concrete_body(kind: TraitKind, eff: &EffType, variant: u8) -> String {
    let body = fallibility_body(
        kind,
        eff.contains(Effect::Primitive(PrimitiveEffect::Fallible)),
        variant,
    );
    if *eff != EffType::all_primitives() {
        return body;
    }
    // All effects: also write and read where the method's own row or its result performs `E`.
    match kind {
        TraitKind::Both | TraitKind::Own | TraitKind::OwnFallible => {
            format!("effects::write(); ({body}) + effects::read()")
        }
        TraitKind::Returned => {
            "{ let v = s.v; |y| { effects::write(); idiv(y, v) + effects::read() } }".into()
        }
        TraitKind::Callback => body,
    }
}

fn fallibility_body(kind: TraitKind, fallible: bool, variant: u8) -> String {
    match (kind, fallible, variant) {
        (TraitKind::Both, false, 0) => "f(x) + s.v".into(),
        (TraitKind::Both, false, _) => "f(f(x) + s.v)".into(),
        (TraitKind::Both, true, 0) => "idiv(f(x), s.v)".into(),
        (TraitKind::Both, true, _) => "f(idiv(x, s.v))".into(),
        (TraitKind::Own, false, 0) => "x + s.v".into(),
        (TraitKind::Own, false, _) => "x * s.v".into(),
        (TraitKind::Own, true, 0) => "idiv(x, s.v)".into(),
        (TraitKind::Own, true, _) => "idiv(s.v, x)".into(),
        (TraitKind::Callback, false, 0) => "f(x) + s.v".into(),
        (TraitKind::Callback, false, _) => "f(f(x))".into(),
        // The method's own row is pure: an impl accepting fallible callbacks cannot call them.
        (TraitKind::Callback, true, _) => "x + s.v".into(),
        (TraitKind::Returned, false, 0) => "|y| y + s.v".into(),
        (TraitKind::Returned, false, _) => "{ let v = s.v; |y| y * v }".into(),
        (TraitKind::Returned, true, 0) => "|y| idiv(y, s.v)".into(),
        (TraitKind::Returned, true, _) => "{ let v = s.v; |y| idiv(v, y) }".into(),
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
