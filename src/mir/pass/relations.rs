// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! What the optimizer knows about integers it does *not* know the value of.
//!
//! [`dataflow`](super::dataflow) answers "which slot holds which constant". This answers the
//! question folding cannot reach: how two unknown quantities are related, so that `i + 1` is one
//! more than `i` and a comparison between them decides a branch. It is the representation layer of
//! bounds-check elimination; recognizing induction and rewriting the checks are separate steps on
//! top of it.
//!
//! # Facts are about values, not about slots
//!
//! MIR is storage-explicit, so a slot's contents change and any fact phrased about the *slot* would
//! have to be thrown away on every write. Facts here are phrased about a [`Symbol`] — the contents
//! one definition put in one place — and a write mints a new symbol rather than contradicting the
//! old one. `i@b1.4 = i@entry + 1` stays true forever, because it is a statement about two values
//! that existed, not about a variable.
//!
//! What a write *does* invalidate is the binding from the place to its current symbol, and every
//! fact reachable only through it. That is the whole of invalidation, and it is why the induction
//! relation survives the assignment that creates it: the fact naming the superseded symbol is kept
//! precisely because the new symbol's own fact names it.
//!
//! A symbol is named by its definition *site*, never by a counter. A counter would mint fresh
//! symbols on every re-walk and the fixpoint would never settle; program points are finite, so the
//! lattice is, and the analysis terminates for the same reason [`dataflow`](super::dataflow) does.
//!
//! # What escapes is not the same question here
//!
//! Folding must escape any place a callee may write through, because it has no way to say what was
//! written. This analysis does have a way, for the callees
//! [`known_callee`](super::known_callee) resolves: an `Iterator::next` writes its iterator's `next`
//! field and captures nothing, so the place stays tracked and the transfer function accounts for
//! the write. That is why the escape scan is parameterized rather than shared wholesale.
//!
//! The place model, the escape scan and the successor walk are
//! [`dataflow`](super::dataflow)'s. The register-to-place binding is not, and is the one thing
//! duplicated between the two; fusing both analyses into a single walk is worth doing once this one
//! has a consumer and the fusion can be measured against it.
//!
//! The consumers are the remaining bounds-check-elimination steps, so the items here are exercised
//! by the tests below until those land.
#![allow(dead_code)]

use std::{
    borrow::Cow,
    cmp::{Ordering, Reverse},
    collections::BinaryHeap,
    fmt,
    ops::Deref,
};

use rustc_hash::{FxHashMap, FxHashSet};
use ustr::Ustr;

use super::{
    dataflow::{PlaceBindings, Root, call_operands, escaping_roots, field_index},
    known_callee::{KnownCallee, KnownCallees, Layouts, RangeLayout},
    site::{OperationIndex, OperationSite},
};
use crate::{
    define_id_type, graph,
    hir::function::ArgConvention,
    mir::{
        self, BlockId, Function, Operation, OperationKind, dominance::Dominance,
        terminator::TerminatorKind, value::ValueId,
    },
    module::{FunctionId, ProjectionIndex, id::Id},
    std::math::Int,
    types::r#type::Type,
};

/// The most terms an affine form may carry.
///
/// A bound rather than a tuning knob: it is what keeps every operation on a form linear in a
/// constant, so the analysis cannot become quadratic in the size of an expression. Index
/// arithmetic reaching this width is not the arithmetic bounds-check elimination is about.
const MAX_TERMS: usize = 4;

/// The most comparisons a state may carry.
///
/// The same kind of bound as [`MAX_TERMS`], for the same reason: this set is compared on every edge
/// the fixpoint walks, and a body of nested conditions would otherwise make each comparison cost
/// the depth it sits at.
const MAX_KNOWN: usize = 8;

/// Which definition put the current contents in a place.
///
/// Program points, so that re-walking a block during the fixpoint produces the same symbols it
/// produced last time.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum DefSite {
    /// The contents on entry to the function: a parameter's incoming value, or whatever an
    /// `alloca` has before anything writes it.
    Entry,
    /// The operation at a position in the body. A block's terminator takes the index one past its
    /// last operation, which is where an `Invoke` call's result is written.
    Operation(OperationSite),
    /// The merge of predecessors that disagreed about which definition supplies the place.
    Join(BlockId),
}

impl DefSite {
    /// Where in its block the operation sits, for a site that names one.
    pub(crate) fn operation_index(&self) -> Option<OperationIndex> {
        match self {
            DefSite::Operation(site) => Some(site.index),
            _ => None,
        }
    }
}

define_id_type!(
    /// A storage slot's dense identity.
    ///
    /// The analysis names slots far more often than it does anything else — every operand read is
    /// one — so a slot has to be a word, not a root plus a heap-allocated path. [`Places`] holds the
    /// tree this indexes into.
    #[derive(PartialOrd, Ord)]
    PlaceId
);

struct PlaceNode {
    root: Root,
    parent: Option<PlaceId>,
    /// The field position this slot sits at in its parent, so a path can be rebuilt when one has
    /// to be replayed against a different base.
    field: Option<ProjectionIndex>,
    /// The slots inside this one that have been named. Forgetting a slot walks this rather than
    /// every slot the body has, which is the difference between linear and quadratic in body size:
    /// a definition forgets what is inside it, and definitions are most of what the analysis does.
    children: Vec<PlaceId>,
}

/// The storage slots one analysis run has named, as a tree.
#[derive(Default)]
pub(crate) struct Places {
    nodes: Vec<PlaceNode>,
    roots: FxHashMap<Root, PlaceId>,
    fields: FxHashMap<(PlaceId, ProjectionIndex), PlaceId>,
}

impl Places {
    fn root(&mut self, root: Root) -> PlaceId {
        if let Some(id) = self.roots.get(&root) {
            return *id;
        }
        let id = self.push(root, None, None);
        self.roots.insert(root, id);
        id
    }

    fn field(&mut self, base: PlaceId, index: ProjectionIndex) -> PlaceId {
        if let Some(id) = self.fields.get(&(base, index)) {
            return *id;
        }
        let id = self.push(self.nodes[base.as_index()].root, Some(base), Some(index));
        self.nodes[base.as_index()].children.push(id);
        self.fields.insert((base, index), id);
        id
    }

    fn push(
        &mut self,
        root: Root,
        parent: Option<PlaceId>,
        field: Option<ProjectionIndex>,
    ) -> PlaceId {
        let id = PlaceId::from_index(self.nodes.len());
        self.nodes.push(PlaceNode {
            root,
            parent,
            field,
            children: Vec::new(),
        });
        id
    }

    pub(crate) fn root_of(&self, place: PlaceId) -> Root {
        self.nodes[place.as_index()].root
    }

    fn parent(&self, place: PlaceId) -> Option<PlaceId> {
        self.nodes[place.as_index()].parent
    }

    fn is_root(&self, place: PlaceId) -> bool {
        self.nodes[place.as_index()].parent.is_none()
    }

    /// The field positions leading from `base` down to `inner`.
    pub(crate) fn path_from(&self, base: PlaceId, inner: PlaceId) -> Vec<ProjectionIndex> {
        let mut path = Vec::new();
        let mut current = inner;
        while current != base {
            let node = &self.nodes[current.as_index()];
            let (Some(parent), Some(field)) = (node.parent, node.field) else {
                break;
            };
            path.push(field);
            current = parent;
        }
        path.reverse();
        path
    }

    /// Visits every slot strictly inside `place`.
    fn inside(&self, place: PlaceId, visit: &mut impl FnMut(PlaceId)) {
        for child in &self.nodes[place.as_index()].children {
            visit(*child);
            self.inside(*child, visit);
        }
    }
}

/// A value the analysis can state facts about.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum Symbol {
    /// The contents a definition put in a place.
    Stored(PlaceId, DefSite),
    /// A materialized register value. MIR registers are single-assignment, so a register names one
    /// value and needs no definition site of its own.
    Register(ValueId),
}

define_id_type!(
    /// A symbol's dense identity, so that a fact is a few machine words rather than a cloned path.
    #[derive(PartialOrd, Ord)]
    SymbolId
);

/// The symbols one analysis run has named.
///
/// Lives beside the flow states rather than inside them: interning is monotone and shared, while a
/// state is cloned at every join.
#[derive(Default)]
pub(crate) struct Symbols {
    ids: FxHashMap<Symbol, SymbolId>,
    names: Vec<Symbol>,
}

impl Symbols {
    fn intern(&mut self, symbol: Symbol) -> SymbolId {
        if let Some(id) = self.ids.get(&symbol) {
            return *id;
        }
        let id = SymbolId::from_index(self.names.len());
        self.names.push(symbol);
        self.ids.insert(symbol, id);
        id
    }

    pub(crate) fn name(&self, id: SymbolId) -> &Symbol {
        &self.names[id.as_index()]
    }

    pub(crate) fn len(&self) -> usize {
        self.names.len()
    }
}

/// The names one analysis run has minted, for slots and for values.
///
/// Lives beside the flow states rather than inside them: interning is monotone and shared, while a
/// state is cloned at every join.
#[derive(Default)]
pub(crate) struct Interner {
    places: Places,
    symbols: Symbols,
    /// Place-producing registers are SSA identities, not flow facts. Once an `alloca` or
    /// `subfield` defines one, every path on which the register may legally be used names the same
    /// place. Keeping that structural map here avoids cloning, joining and comparing it in every
    /// block state.
    register_places: FxHashMap<ValueId, PlaceId>,
}

impl Interner {
    fn place_root(&mut self, root: Root) -> PlaceId {
        self.places.root(root)
    }

    fn place_field(&mut self, base: PlaceId, index: ProjectionIndex) -> PlaceId {
        self.places.field(base, index)
    }

    fn symbol(&mut self, symbol: Symbol) -> SymbolId {
        self.symbols.intern(symbol)
    }

    fn bind_register_place(&mut self, register: ValueId, place: PlaceId) -> bool {
        match self.register_places.insert(register, place) {
            Some(existing) => {
                assert_eq!(
                    existing, place,
                    "an SSA register cannot denote two different places"
                );
                false
            }
            None => true,
        }
    }

    fn register_place(&self, register: ValueId) -> Option<PlaceId> {
        self.register_places.get(&register).copied()
    }

    pub(crate) fn places(&self) -> &Places {
        &self.places
    }

    pub(crate) fn symbols(&self) -> &Symbols {
        &self.symbols
    }
}

/// `constant + Σ coefficient × symbol`.
///
/// Ferlium's `int` wraps, and so does this: every combination below is computed with wrapping
/// arithmetic, so a form is an exact statement about the machine integers rather than an
/// approximation of mathematical ones. A consumer reasoning about magnitudes must account for that
/// itself.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(crate) struct Affine {
    pub constant: Int,
    terms: Terms,
}

/// An affine form's terms: sorted by symbol, never holding a zero coefficient, never longer than
/// [`MAX_TERMS`].
///
/// A fixed array, as the bound allows, so that a form is plain data and copying a state's facts
/// allocates nothing. Only the first `len` entries are terms, which is why comparison is over the
/// slice they form rather than derived.
#[derive(Clone, Copy)]
struct Terms {
    len: u8,
    entries: [(SymbolId, Int); MAX_TERMS],
}

impl Terms {
    const EMPTY: Terms = Terms {
        len: 0,
        entries: [(SymbolId::new(0), 0); MAX_TERMS],
    };

    /// Terms from ones sorted by symbol, dropping zero coefficients, or `None` past the bound.
    fn from_sorted(terms: impl IntoIterator<Item = (SymbolId, Int)>) -> Option<Terms> {
        let mut result = Terms::EMPTY;
        for (symbol, coefficient) in terms {
            if coefficient == 0 {
                continue;
            }
            let len = usize::from(result.len);
            if len == MAX_TERMS {
                return None;
            }
            debug_assert!(
                len == 0 || result.entries[len - 1].0 < symbol,
                "terms arrive sorted and distinct"
            );
            result.entries[len] = (symbol, coefficient);
            result.len += 1;
        }
        Some(result)
    }
}

impl Deref for Terms {
    type Target = [(SymbolId, Int)];

    fn deref(&self) -> &Self::Target {
        &self.entries[..usize::from(self.len)]
    }
}

impl PartialEq for Terms {
    fn eq(&self, other: &Self) -> bool {
        **self == **other
    }
}

impl Eq for Terms {}

impl PartialOrd for Terms {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Terms {
    fn cmp(&self, other: &Self) -> Ordering {
        (**self).cmp(&**other)
    }
}

impl fmt::Debug for Terms {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl Affine {
    pub(crate) fn constant(value: Int) -> Self {
        Self {
            constant: value,
            terms: Terms::EMPTY,
        }
    }

    pub(crate) fn symbol(symbol: SymbolId) -> Self {
        Self {
            constant: 0,
            terms: Terms::from_sorted([(symbol, 1)]).expect("one term is within the bound"),
        }
    }

    pub(crate) fn terms(&self) -> &[(SymbolId, Int)] {
        &self.terms
    }

    /// The constant this form is, if it is one.
    pub(crate) fn as_constant(&self) -> Option<Int> {
        self.terms.is_empty().then_some(self.constant)
    }

    /// The single symbol this form is, if it is exactly one symbol with no offset.
    pub(crate) fn as_symbol(&self) -> Option<SymbolId> {
        match *self.terms {
            [(symbol, 1)] if self.constant == 0 => Some(symbol),
            _ => None,
        }
    }

    /// `self + other`, or `None` when the sum would exceed [`MAX_TERMS`].
    pub(crate) fn add(&self, other: &Affine) -> Option<Affine> {
        // Both sides are sorted, so their sum is a merge.
        let (mut ours, mut theirs) = (
            self.terms.iter().copied().peekable(),
            other.terms.iter().copied().peekable(),
        );
        let merged = std::iter::from_fn(|| match (ours.peek().copied(), theirs.peek().copied()) {
            (Some((a, x)), Some((b, y))) => match a.cmp(&b) {
                Ordering::Less => ours.next(),
                Ordering::Greater => theirs.next(),
                Ordering::Equal => {
                    ours.next();
                    theirs.next();
                    Some((a, x.wrapping_add(y)))
                }
            },
            _ => ours.next().or_else(|| theirs.next()),
        });
        Some(Affine {
            constant: self.constant.wrapping_add(other.constant),
            terms: Terms::from_sorted(merged)?,
        })
    }

    pub(crate) fn sub(&self, other: &Affine) -> Option<Affine> {
        self.add(&other.scale(-1))
    }

    /// `self × factor`. A wrapping product may vanish, and then its term goes.
    pub(crate) fn scale(&self, factor: Int) -> Affine {
        let terms = self
            .terms
            .iter()
            .map(|&(symbol, coefficient)| (symbol, coefficient.wrapping_mul(factor)));
        Affine {
            constant: self.constant.wrapping_mul(factor),
            terms: Terms::from_sorted(terms).expect("scaling adds no term"),
        }
    }

    /// `self × other`, which stays affine only when one side is a constant.
    pub(crate) fn mul(&self, other: &Affine) -> Option<Affine> {
        match (self.as_constant(), other.as_constant()) {
            (Some(factor), _) => Some(other.scale(factor)),
            (_, Some(factor)) => Some(self.scale(factor)),
            _ => None,
        }
    }
}

/// How two quantities compare.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub(crate) enum Comparison {
    Less,
    LessOrEqual,
    Equal,
    NotEqual,
}

/// `left ⋈ right`.
///
/// Ferlium's `int` wraps, so only an equality may be moved to one side: subtraction is a bijection,
/// which makes `l == r` and `l - r == 0` one fact, but `x + 1 < x` holds at the maximum where
/// `1 < 0` never does. An equality is therefore stored as `difference == 0`, with the difference's
/// sign chosen canonically, and an order keeps both sides as written.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(crate) struct Predicate {
    pub left: Affine,
    pub comparison: Comparison,
    pub right: Affine,
}

impl Predicate {
    /// `left ⋈ right`, normalized. `None` when an equality's difference is not affine.
    pub(crate) fn between(left: &Affine, comparison: Comparison, right: &Affine) -> Option<Self> {
        Some(match comparison {
            Comparison::Less | Comparison::LessOrEqual => Self {
                left: *left,
                comparison,
                right: *right,
            },
            Comparison::Equal | Comparison::NotEqual => {
                let difference = left.sub(right)?;
                let flipped = difference.scale(-1);
                Self {
                    left: difference.min(flipped),
                    comparison,
                    right: Affine::constant(0),
                }
            }
        })
    }

    /// The predicate that holds exactly when this one does not: `¬(l < r)` is `r <= l`.
    pub(crate) fn negated(&self) -> Self {
        let (left, right) = match self.comparison {
            Comparison::Less | Comparison::LessOrEqual => (&self.right, &self.left),
            Comparison::Equal | Comparison::NotEqual => (&self.left, &self.right),
        };
        Self {
            left: *left,
            comparison: match self.comparison {
                Comparison::Less => Comparison::LessOrEqual,
                Comparison::LessOrEqual => Comparison::Less,
                Comparison::Equal => Comparison::NotEqual,
                Comparison::NotEqual => Comparison::Equal,
            },
            right: *right,
        }
    }

    /// Whether this holds outright: both sides constant, or one form on both.
    fn is_certain(&self) -> Option<bool> {
        let (left, right) = match (self.left.as_constant(), self.right.as_constant()) {
            (Some(left), Some(right)) => (left, right),
            _ if self.left == self.right => (0, 0),
            _ => return None,
        };
        Some(match self.comparison {
            Comparison::Less => left < right,
            Comparison::LessOrEqual => left <= right,
            Comparison::Equal => left == right,
            Comparison::NotEqual => left != right,
        })
    }

    /// Whether holding `self` means `goal` holds too.
    ///
    /// **Deliberately syntactic.** Shifting both sides of an order by one offset is unsound on a
    /// wrapping `int`. The one shift allowed is the strictness step: `l < r` puts `l` below the
    /// maximum and `r` above the minimum, so `l + 1 <= r` and `l <= r - 1` cannot have wrapped.
    fn entails(&self, goal: &Predicate) -> bool {
        if self == goal {
            return true;
        }
        if self.comparison != Comparison::Less {
            return false;
        }
        let one = Affine::constant(1);
        match goal.comparison {
            Comparison::LessOrEqual => {
                (goal.left == self.left && goal.right == self.right)
                    || (goal.right == self.right
                        && self.left.add(&one).as_ref() == Some(&goal.left))
                    || (goal.left == self.left
                        && self.right.sub(&one).as_ref() == Some(&goal.right))
            }
            Comparison::NotEqual => {
                Predicate::between(&self.left, Comparison::NotEqual, &self.right).as_ref()
                    == Some(goal)
            }
            Comparison::Less | Comparison::Equal => false,
        }
    }
}

/// What is known about one symbol.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) enum Fact {
    /// The symbol's value, as an affine form over other symbols.
    Value(Affine),
    /// The symbol is the `Ordering` two quantities compare to. Carried whole rather than as three
    /// predicates because which of them is asked for is decided later, by the tag a `comp_eq`
    /// tests.
    Ordering { left: Affine, right: Affine },
    /// The symbol is a boolean, true exactly when this holds.
    Truth(Predicate),
    /// The internal array predicate is true exactly when both signed bounds hold.
    /// Its length argument must be nonnegative; failure is a disjunction, not two negated facts.
    InBounds { offset: Affine, length: Affine },
    /// The symbol is a boolean whose truth *implies* these, without the converse.
    ///
    /// Separate from [`Truth`](Self::Truth) because one direction is all a yielded option gives:
    /// the payload is in range when the option is `Some`, and nothing follows from it being `None`.
    Implies(Vec<Predicate>),
    /// The symbol is an `Option` a range iterator yielded.
    ///
    /// `value` is the iterator's cursor before the step, which is what the payload holds;
    /// `present_when` is what that value satisfies when the option is `Some`. Attached to the option
    /// itself rather than to the payload slot, because where the payload sits inside an `Option` is
    /// a layout detail — a read looks *up* from its own place to find this.
    Yield {
        value: SymbolId,
        present_when: Vec<Predicate>,
    },
}

/// Captured before a storage transfer invalidates either place's current definitions.
struct PlaceContents {
    value: Option<Fact>,
    fields: Vec<(Vec<ProjectionIndex>, Fact)>,
}

/// The relational state at one program point.
#[derive(Clone, PartialEq, Eq, Default, Debug)]
pub(crate) struct State {
    /// The symbol currently supplying each tracked place — the symbol itself rather than the
    /// definition that minted it, so that reading a slot is one lookup on a word key instead of a
    /// lookup followed by an interning of a composite name.
    ///
    /// A place absent from here has never been written in this function, and takes
    /// [`DefSite::Entry`].
    current: FxHashMap<PlaceId, SymbolId>,
    /// What is known about a symbol. A symbol absent from here is an unknown quantity, which is
    /// still a quantity: it can be named, and two uses of it are the same value.
    facts: FxHashMap<SymbolId, Fact>,
    /// Comparisons that hold at this point, sorted and deduplicated so that two states holding the
    /// same set compare equal — which is what the fixpoint tests.
    known: Vec<Predicate>,
}

impl State {
    fn place_contents(&mut self, place: Option<PlaceId>, interner: &mut Interner) -> PlaceContents {
        let value = place.map(|place| self.place_value_fact(place, interner));
        let fields = place
            .map(|place| {
                self.within(place, interner.places())
                    .into_iter()
                    .map(|inner| {
                        let fact = self.place_value_fact(inner, interner);
                        (interner.places().path_from(place, inner), fact)
                    })
                    .collect()
            })
            .unwrap_or_default();
        PlaceContents { value, fields }
    }

    fn place_value_fact(&mut self, place: PlaceId, interner: &mut Interner) -> Fact {
        let symbol = self.symbol_of(place, interner);
        self.fact(symbol)
            .cloned()
            .unwrap_or_else(|| Fact::Value(Affine::symbol(symbol)))
    }

    fn define_contents(
        &mut self,
        place: PlaceId,
        def: DefSite,
        interner: &mut Interner,
        mut contents: PlaceContents,
    ) {
        self.define(place, def, interner, contents.value);
        // A parent definition forgets its children, so install shallowest fields first.
        contents.fields.sort_by_key(|(path, _)| path.len());
        for (path, fact) in contents.fields {
            let mut inner = place;
            for index in path {
                inner = interner.place_field(inner, index);
            }
            self.define(inner, def, interner, Some(fact));
        }
    }

    /// The symbol a place's current contents are.
    pub(crate) fn symbol_of(&self, place: PlaceId, interner: &mut Interner) -> SymbolId {
        match self.current.get(&place) {
            Some(symbol) => *symbol,
            None => interner.symbol(Symbol::Stored(place, DefSite::Entry)),
        }
    }

    pub(crate) fn fact(&self, symbol: SymbolId) -> Option<&Fact> {
        self.facts.get(&symbol)
    }

    /// Records what is known about a symbol, or that nothing is.
    fn set_fact(&mut self, symbol: SymbolId, fact: Option<Fact>) {
        match fact {
            Some(fact) => {
                self.facts.insert(symbol, fact);
            }
            None => {
                self.facts.remove(&symbol);
            }
        }
    }

    /// The comparisons known to hold here.
    pub(crate) fn known(&self) -> &[Predicate] {
        &self.known
    }

    /// Whether `goal` follows from what is known here.
    pub(crate) fn implies(&self, goal: &Predicate) -> bool {
        self.holds(goal) || self.holds_by_offset(goal)
    }

    /// Whether `goal` is certain or entailed by one known fact.
    fn holds(&self, goal: &Predicate) -> bool {
        goal.is_certain()
            .unwrap_or_else(|| self.known.iter().any(|fact| fact.entails(goal)))
    }

    /// `r + d ⋈ r` from `0 <= r` and `d ⋈ 0`: a non-positive offset from a non-negative value
    /// cannot wrap. This is how `len + i < len` follows from `i < 0` for an array's length.
    fn holds_by_offset(&self, goal: &Predicate) -> bool {
        if !matches!(goal.comparison, Comparison::Less | Comparison::LessOrEqual) {
            return false;
        }
        let Some(offset) = goal.left.sub(&goal.right) else {
            return false;
        };
        let zero = Affine::constant(0);
        self.holds(&Predicate {
            left: zero,
            comparison: Comparison::LessOrEqual,
            right: goal.right,
        }) && self.holds(&Predicate {
            left: offset,
            comparison: goal.comparison,
            right: zero,
        })
    }

    /// Records a comparison that holds from here on.
    ///
    /// Bounded: a chain of nested conditions would otherwise carry every guard it passed under into
    /// every block below, and the set is a state the fixpoint compares on every edge. Sorted order
    /// makes which ones survive a property of the facts rather than of the walk.
    fn assume(&mut self, predicate: Predicate) {
        // One that holds outright is already answered by `implies`, and the room it would take is
        // room a fact about a symbol needs. A check on a constant index states one of these.
        if predicate.is_certain() == Some(true) {
            return;
        }
        if let Err(index) = self.known.binary_search(&predicate) {
            self.known.insert(index, predicate);
            self.known.truncate(MAX_KNOWN);
        }
    }

    /// The form of a value read through a call argument, for a consumer asking about one operand.
    pub(crate) fn argument_affine(
        &self,
        operand: &mir::Value,
        interner: &mut Interner,
    ) -> Option<Affine> {
        argument_affine(operand, interner, self)
    }

    /// The slot an operand names, if it names one.
    pub(crate) fn place_of(
        &self,
        operand: &mir::Value,
        interner: &mut Interner,
    ) -> Option<PlaceId> {
        match operand {
            mir::Value::Register(id) => interner.register_place(*id),
            mir::Value::Parameter(id) => Some(interner.place_root(Root::Parameter(*id))),
            _ => None,
        }
    }

    /// The affine form of a place's contents.
    ///
    /// A place with nothing known is still one value, and naming it is what relates its two uses.
    /// Before falling back to that, the ancestors are consulted: a range iterator's yield is
    /// recorded on the `Option` as a whole, so reading the payload — however deep inside the option
    /// it sits — has to find it.
    pub(crate) fn place_affine(&self, place: PlaceId, interner: &mut Interner) -> Affine {
        let symbol = self.symbol_of(place, interner);
        if let Some(Fact::Value(affine)) = self.fact(symbol) {
            return *affine;
        }
        let mut ancestor = place;
        while let Some(above) = interner.places.parent(ancestor) {
            ancestor = above;
            let symbol = self.symbol_of(ancestor, interner);
            if let Some(Fact::Yield { value, .. }) = self.fact(symbol) {
                return Affine::symbol(*value);
            }
        }
        Affine::symbol(symbol)
    }

    /// Every tracked slot inside `place`.
    fn within(&self, place: PlaceId, places: &Places) -> Vec<PlaceId> {
        let mut inside = Vec::new();
        places.inside(place, &mut |child| {
            if self.current.contains_key(&child) {
                inside.push(child);
            }
        });
        inside
    }

    /// Rebinds `place` to a definition, and forgets what was known about the slots inside it.
    ///
    /// The superseded symbol keeps its fact: it names a value that existed, and a fact about the
    /// *new* contents may well be stated in terms of it. What stops those accumulating is that the
    /// symbol universe is the finite set of program points.
    fn define(
        &mut self,
        place: PlaceId,
        def: DefSite,
        interner: &mut Interner,
        fact: Option<Fact>,
    ) {
        // Only the subtree, not every slot in the body: `inside` walks the interned tree.
        let mut forgotten = Vec::new();
        interner
            .places
            .inside(place, &mut |child| forgotten.push(child));
        for child in forgotten {
            self.current.remove(&child);
        }
        let symbol = interner.symbol(Symbol::Stored(place, def));
        self.current.insert(place, symbol);
        self.set_fact(symbol, fact);
    }

    /// Stops tracking a place whose storage lifetime has ended.
    fn forget(&mut self, place: PlaceId, interner: &mut Interner) {
        let mut forgotten = vec![place];
        interner
            .places
            .inside(place, &mut |child| forgotten.push(child));
        for child in forgotten {
            self.current.remove(&child);
        }
    }

    fn common_facts_and_predicates(
        &self,
        other: &State,
    ) -> (FxHashMap<SymbolId, Fact>, Vec<Predicate>) {
        let mut facts = FxHashMap::default();
        for (symbol, fact) in &self.facts {
            if other.facts.get(symbol) == Some(fact) {
                facts.insert(*symbol, fact.clone());
            }
        }
        // Both inputs are sorted. Intersect them as such instead of doing up to eight linear
        // `contains` scans for every join.
        let mut known = Vec::with_capacity(self.known.len().min(other.known.len()));
        let (mut ours, mut theirs) = (0, 0);
        while ours < self.known.len() && theirs < other.known.len() {
            match self.known[ours].cmp(&other.known[theirs]) {
                Ordering::Less => ours += 1,
                Ordering::Greater => theirs += 1,
                Ordering::Equal => {
                    known.push(self.known[ours].clone());
                    ours += 1;
                    theirs += 1;
                }
            }
        }
        (facts, known)
    }
}

/// The type of storage each root holds, as the body declares it.
///
/// An interned place carries no type — only a root and field positions — so recognizing that a slot
/// is an array's length, or a range iterator, means going back to where its stack storage was
/// declared. Run-time allocations are byte extents whose pointee type does not describe the whole
/// allocation, so they are deliberately absent.
struct RootTypes {
    allocas: FxHashMap<ValueId, Type>,
    parameters: Vec<Type>,
}

impl RootTypes {
    fn new(func: &Function) -> Self {
        let mut allocas = FxHashMap::default();
        for block in func.blocks() {
            for operation in func.block(block).operations() {
                if let OperationKind::Alloca { ty } = &operation.kind
                    && let Some(result) = operation.result_id()
                {
                    allocas.insert(result, *ty);
                }
            }
        }
        Self {
            allocas,
            parameters: func.parameters().iter().map(|p| p.ty).collect(),
        }
    }

    fn of(&self, root: Root) -> Option<Type> {
        match root {
            Root::Alloca(id) => self.allocas.get(&id).copied(),
            Root::Parameter(id) => self.parameters.get(id.as_index()).copied(),
            Root::DictEntry(_) => None,
        }
    }
}

/// The result of analysing a function.
pub(crate) struct Analysis {
    entry_states: FxHashMap<BlockId, State>,
    exit_states: FxHashMap<BlockId, State>,
    interner: Interner,
    escaped: FxHashSet<Root>,
    types: RootTypes,
    inductions: FxHashMap<Root, Induction>,
}

impl Analysis {
    /// The state on entry to a block, for a block the analysis reached.
    pub(crate) fn entry_state(&self, block: BlockId) -> Option<&State> {
        self.entry_states.get(&block)
    }

    /// The state after a block's last operation, including its terminator's call.
    pub(crate) fn exit_state(&self, block: BlockId) -> Option<&State> {
        self.exit_states.get(&block)
    }

    /// Whether the edge from `block` into `successor` is never taken, as a proof: a block the
    /// analysis did not reach claims nothing.
    pub(crate) fn edge_is_dead(
        &mut self,
        func: &Function,
        known: &KnownCallees,
        original_of: &dyn Fn(FunctionId) -> Option<FunctionId>,
        block: BlockId,
        successor: BlockId,
    ) -> bool {
        let Some(exit) = self.exit_states.get(&block) else {
            return false;
        };
        let context = Context {
            func,
            semantics: Semantics { known, original_of },
            escaped: &self.escaped,
            types: &self.types,
            inductions: &self.inductions,
        };
        let terminator = &func.block(block).terminator().kind;
        refine(exit, terminator, successor, &context, &mut self.interner).is_none()
    }

    /// Replays a block from its entry state, handing each operation the state that reaches it.
    ///
    /// The state a rewrite needs is the one at its own call site, which is mid-block and which
    /// storing every program point would make the analysis pay for in memory. Replaying is exact:
    /// the entry states are final, and the transfer function is deterministic, so this walks the
    /// same values the fixpoint settled on.
    pub(crate) fn replay(
        &mut self,
        func: &Function,
        known: &KnownCallees,
        original_of: &dyn Fn(FunctionId) -> Option<FunctionId>,
        block: BlockId,
        mut visit: impl FnMut(&Operation, DefSite, &State, &mut Interner, &Context<'_>),
    ) {
        // Borrowed, never rebuilt: this is called once per block, and re-deriving the root types
        // each time would rescan the whole body per block.
        let context = Context {
            func,
            semantics: Semantics { known, original_of },
            escaped: &self.escaped,
            types: &self.types,
            inductions: &self.inductions,
        };
        let Some(mut state) = self.entry_states.get(&block).cloned() else {
            return;
        };
        for (index, operation) in func.block(block).operations().iter().enumerate() {
            let def = site(block, index);
            visit(operation, def, &state, &mut self.interner, &context);
            transfer(operation, def, &context, &mut self.interner, &mut state);
        }
        if let TerminatorKind::Invoke { operation, .. } = &func.block(block).terminator().kind {
            let def = site(block, func.block(block).operations().len());
            visit(operation, def, &state, &mut self.interner, &context);
        }
    }

    pub(crate) fn symbols(&self) -> &Symbols {
        self.interner.symbols()
    }

    pub(crate) fn is_escaped(&self, root: &Root) -> bool {
        self.escaped.contains(root)
    }
}

/// A range loop whose induction [`recognize`] proved.
#[derive(Clone, Copy, Debug)]
struct Induction {
    layout: RangeLayout,
    /// Whether the upper bound is part of the range.
    inclusive: bool,
    /// The cursor's non-negative constant start, retained to state the `start <= end` obligation
    /// that distinguishes an ascending range from a descending one.
    start: Int,
    /// The one block writing the iterator outside its steps, which dominates every step.
    construction: BlockId,
}

/// Everything one analysis run reads and never changes.
pub(crate) struct Context<'a> {
    func: &'a Function,
    semantics: Semantics<'a>,
    escaped: &'a FxHashSet<Root>,
    types: &'a RootTypes,
    /// Iterator storage whose cursor starts at a non-negative constant. A yielded value receives
    /// ascending bounds only where the flow state separately proves `start <= end`.
    inductions: &'a FxHashMap<Root, Induction>,
}

impl Context<'_> {
    /// The signed index and array length named by a checked `array_index` call.
    ///
    /// Escaped arrays are refused: an opaque mutation could have changed their length without the
    /// relational state seeing a new definition. The callee identity supplies the array type, but
    /// checking the root type as well keeps the positional `len` field meaning explicit.
    pub(crate) fn array_index_forms(
        &self,
        operation: &Operation,
        state: &State,
        interner: &mut Interner,
    ) -> Option<(Affine, Affine)> {
        if self.semantics.of(operation)? != KnownCallee::ArrayIndex {
            return None;
        }
        let OperationKind::Call { ty, .. } = &operation.kind else {
            return None;
        };
        let call = call_operands(&operation.operands, ty)?;
        if call.arguments.len() != 2 {
            return None;
        }
        let array = tracked_place(state, call.arguments[0].0, self.escaped, interner)?;
        let root = interner.places().root_of(array);
        if !self
            .types
            .of(root)
            .is_some_and(|ty| self.semantics.known.is_array(ty))
        {
            return None;
        }
        let index = state.argument_affine(call.arguments[1].0, interner)?;
        let len = interner.place_field(array, self.semantics.known.layouts().array_len);
        Some((index, state.place_affine(len, interner)))
    }
}

/// Resolves a call's callee to the semantics the optimizer knows for it.
///
/// Boxed as one closure because both the escape scan and the transfer function ask the same
/// question, once before the walk and once during it.
#[derive(Clone, Copy)]
struct Semantics<'a> {
    known: &'a KnownCallees,
    original_of: &'a dyn Fn(FunctionId) -> Option<FunctionId>,
}

impl Semantics<'_> {
    fn of(&self, operation: &Operation) -> Option<KnownCallee> {
        let OperationKind::Call { .. } = &operation.kind else {
            return None;
        };
        let mir::Value::Function(callee) = operation.operands.first()? else {
            return None;
        };
        self.known.resolve(*callee, self.original_of)
    }
}

/// Whether a body has anything for this analysis to say.
///
/// A single linear scan, and the answer is no for most functions: the analysis costs two walks to a
/// fixpoint, and a consumer that runs it on every body in every round would pay that for the many
/// that contain no checked subscript at all. Cheap enough to run before deciding, which is the point
/// — the same shape as the final devirtualization sweep's syntactic filter.
pub(crate) fn worth_analyzing(
    func: &Function,
    known: &KnownCallees,
    original_of: &dyn Fn(FunctionId) -> Option<FunctionId>,
) -> bool {
    let semantics = Semantics { known, original_of };
    // A diverging call is what an inlined check guards, and a range iterator is what a loop's
    // induction lives in.
    let candidate = |operation: &Operation| {
        operation.diverges()
            || matches!(
                semantics.of(operation),
                Some(KnownCallee::ArrayResolveIndex | KnownCallee::ArrayIndex)
            )
            || matches!(&operation.kind, OperationKind::Alloca { ty } if known.range_iterator(*ty).is_some())
    };
    func.blocks().any(|block| {
        func.block(block).operations().iter().any(candidate)
            || matches!(
                &func.block(block).terminator().kind,
                TerminatorKind::Invoke { operation, .. } if candidate(operation)
            )
    })
}

/// The semantics the optimizer knows for an operation's callee, for a consumer that has to ask the
/// same question the analysis does and must ask it the same way.
pub(crate) fn resolved_callee(
    operation: &Operation,
    known: &KnownCallees,
    original_of: &dyn Fn(FunctionId) -> Option<FunctionId>,
) -> Option<KnownCallee> {
    Semantics { known, original_of }.of(operation)
}

/// Runs the analysis to fixpoint over `func`.
///
/// Induction recognition is a bounded local interpretation of each iterator's construction block,
/// performed before the one whole-function fixed point. It deliberately refuses an initializer
/// whose value has to be discovered through another block; falling back to a checked access is
/// cheaper and safer than running the complete relational analysis once merely to inspect two
/// constants and then running it all over again.
pub(crate) fn analyze(
    func: &Function,
    known: &KnownCallees,
    original_of: &dyn Fn(FunctionId) -> Option<FunctionId>,
) -> Analysis {
    let semantics = Semantics { known, original_of };
    // A known callee writes only through the arguments it declares and captures none of them, so
    // its mutable argument stays tracked and `transfer` accounts for the write. A `drop` likewise:
    // it ends a value's life rather than writing another one, and forgetting the place is exactly
    // what the transfer function does. Folding cannot say either, which is why it escapes both —
    // and why an array read only for its length would otherwise be untracked from its own drop.
    let (escaped, register_places) = escaping_roots(func, &|operation| {
        matches!(
            operation.kind,
            OperationKind::Drop { .. } | OperationKind::DropInitialized { .. }
        ) || semantics.of(operation).is_some()
    });

    let types = RootTypes::new(func);
    let no_inductions = FxHashMap::default();
    let context = Context {
        func,
        semantics,
        escaped: &escaped,
        types: &types,
        inductions: &no_inductions,
    };
    // An inlined step is assumed to keep its induction's invariant, then checked against the settled
    // states. An induction with an unproved step is refuted and the analysis rerun; each rerun
    // refutes one of finitely many inductions.
    let mut refuted = FxHashSet::default();
    loop {
        let mut interner = Interner::default();
        seed_register_places(func, &escaped, &mut interner);
        let mut recognized = recognize(&context, &register_places, &mut interner);
        recognized
            .inductions
            .retain(|root, _| !refuted.contains(root));
        let context = Context {
            inductions: &recognized.inductions,
            ..context
        };
        let mut settled = run(&context, recognized.dominance.as_ref(), interner);
        let unproved = unproved_steps(&context, &recognized.steps, &mut settled);
        if unproved.is_empty() {
            return Analysis {
                entry_states: settled.entry_states,
                exit_states: settled.exit_states,
                interner: settled.interner,
                escaped,
                types,
                inductions: recognized.inductions,
            };
        }
        refuted.extend(unproved);
    }
}

/// The inductions whose inlined steps the settled states do not show keeping the invariant.
///
/// A step keeps `start <= end ⇒ start <= cursor` when it adds one to a cursor proved below `end`,
/// which cannot wrap, or when it runs where `end < start`, since the range is never written again
/// and the implication then holds vacuously. A step the analysis never reaches cannot run.
fn unproved_steps(
    context: &Context<'_>,
    steps: &[(Root, OperationSite)],
    settled: &mut Run,
) -> FxHashSet<Root> {
    let mut unproved = FxHashSet::default();
    let mut steps: Vec<_> = steps.iter().map(|&(root, step)| (step, root)).collect();
    steps.sort_unstable_by_key(|(step, _)| (step.block.as_index(), step.index.as_index()));
    // One replay per block, checking each step as the replay reaches it.
    for group in steps.chunk_by(|(a, _), (b, _)| a.block == b.block) {
        let block_id = group[0].0.block;
        let Some(entry) = settled.entry_states.get(&block_id) else {
            continue;
        };
        let interner = &mut settled.interner;
        let mut state = entry.clone();
        let block = context.func.block(block_id);
        let invoked = match &block.terminator().kind {
            TerminatorKind::Invoke { operation, .. } => Some(operation),
            _ => None,
        };
        let mut pending = group.iter().peekable();
        for (index, operation) in block.operations().iter().chain(invoked).enumerate() {
            if pending.peek().is_none() {
                break;
            }
            // The steps here not already vacuous, with the cursor they must leave one higher.
            let mut incrementing = Vec::new();
            while let Some(&(_, root)) = pending.next_if(|(step, _)| step.index.as_index() == index)
            {
                let Some(induction) = context.inductions.get(&root) else {
                    continue;
                };
                let iterator = interner.place_root(root);
                let cursor = interner.place_field(iterator, induction.layout.next);
                let range = interner.place_field(iterator, induction.layout.range);
                let end = interner.place_field(range, induction.layout.end);
                let end = state.place_affine(end, interner);
                let before = state.place_affine(cursor, interner);
                let start = Affine::constant(induction.start);
                let guarded = |predicate: Option<Predicate>| {
                    predicate.is_some_and(|predicate| state.implies(&predicate))
                };
                if guarded(Predicate::between(&end, Comparison::Less, &start)) {
                    continue;
                }
                let below_end = guarded(Predicate::between(&before, Comparison::Less, &end));
                let incremented = before.add(&Affine::constant(1)).filter(|_| below_end);
                incrementing.push((root, cursor, incremented));
            }
            transfer(
                operation,
                site(block_id, index),
                context,
                interner,
                &mut state,
            );
            for (root, cursor, incremented) in incrementing {
                if incremented != Some(state.place_affine(cursor, interner)) {
                    unproved.insert(root);
                }
            }
        }
        assert!(pending.peek().is_none(), "a step site names an operation");
    }
    unproved
}

/// One run of the fixpoint.
struct Run {
    entry_states: FxHashMap<BlockId, State>,
    exit_states: FxHashMap<BlockId, State>,
    interner: Interner,
}

/// The rounds one run may take before it is abandoned.
///
/// Generous: bodies are small and each round is one walk. It exists because the state is not
/// provably monotone — bounding [`MAX_KNOWN`] means a smaller input can keep a *different* eight
/// predicates, so two rounds could in principle alternate. Rather than reason about that, a run
/// that has not settled by here reports nothing at all, which is always sound.
const MAX_ROUNDS: usize = 64;

/// Walks the body until the entry states stop moving.
///
/// Each round recomputes every block's entry from its predecessors' *current* exits, rather than
/// folding each edge into an accumulated entry as it is walked. The difference matters at a loop
/// header: the back edge's first visit carries facts about the cursor as the construction defined
/// it, and its second about the cursor as the join defines it. Intersecting those two across
/// rounds throws away both, and with them every bound the loop was analysed for.
fn run(context: &Context<'_>, dominance: Option<&Dominance>, mut interner: Interner) -> Run {
    let func = context.func;
    let block_count = func.blocks().count();
    let mut predecessors: Vec<Vec<BlockId>> = vec![Vec::new(); block_count];
    let mut successor_lists: Vec<Vec<usize>> = vec![Vec::new(); block_count];
    for block in func.blocks() {
        for successor in func.block(block).terminator().successors() {
            predecessors[successor.as_index()].push(block);
            successor_lists[block.as_index()].push(successor.as_index());
        }
    }

    // Forward dataflow converges fastest when definitions are visited before their uses and loop
    // back edges last. Block ids are only construction order after edits, so derive reverse
    // postorder from the actual CFG and use it as worklist priority.
    let mut reverse_postorder = vec![usize::MAX; block_count];
    for (index, block) in graph::reverse_postorder(&successor_lists, func.entry().as_index())
        .into_iter()
        .enumerate()
    {
        reverse_postorder[block] = index;
    }

    let mut entry_states: FxHashMap<BlockId, State> = FxHashMap::default();
    let mut exit_states: FxHashMap<BlockId, State> = FxHashMap::default();

    // A worklist rather than a sweep over every block each round: a block's entry can only have
    // moved if a predecessor's exit did, so sweeping recomputes states that cannot have changed and
    // clones each of them to do it.
    let mut queued = vec![false; block_count];
    let mut worklist = BinaryHeap::new();
    worklist.push(Reverse((
        reverse_postorder[func.entry().as_index()],
        func.entry().as_index(),
    )));
    queued[func.entry().as_index()] = true;
    let mut steps = 0usize;
    let budget = MAX_ROUNDS * block_count.max(1);

    while let Some(Reverse((_, block))) = worklist.pop() {
        let block_id = BlockId::from_index(block);
        queued[block_id.as_index()] = false;
        steps += 1;
        if steps > budget {
            return Run {
                entry_states: FxHashMap::default(),
                exit_states: FxHashMap::default(),
                interner,
            };
        }

        // The entry block's state is not a join of anything; every other block's is the join of
        // what each predecessor sends down the edge into it.
        let entry = if block_id == func.entry() {
            State::default()
        } else {
            let mut joined: Option<State> = None;
            for predecessor in &predecessors[block_id.as_index()] {
                let Some(exit) = exit_states.get(predecessor) else {
                    continue;
                };
                let terminator = &func.block(*predecessor).terminator().kind;
                let Some(edge) = refine(exit, terminator, block_id, context, &mut interner) else {
                    continue;
                };
                joined = Some(match joined {
                    Some(existing) => rejoin(&existing, &edge, block_id, &mut interner),
                    None => edge.into_owned(),
                });
            }
            let Some(mut joined) = joined else {
                continue;
            };
            if let Some(dominance) = dominance {
                state_cursor_invariants(&mut joined, block_id, context, dominance, &mut interner);
            }
            joined
        };
        if entry_states.get(&block_id) == Some(&entry) && exit_states.contains_key(&block_id) {
            continue;
        }

        let mut state = entry.clone();
        entry_states.insert(block_id, entry);
        let block = func.block(block_id);
        for (index, operation) in block.operations().iter().enumerate() {
            transfer(
                operation,
                site(block_id, index),
                context,
                &mut interner,
                &mut state,
            );
        }
        if let TerminatorKind::Invoke { operation, .. } = &block.terminator().kind {
            transfer(
                operation,
                site(block_id, block.operations().len()),
                context,
                &mut interner,
                &mut state,
            );
        }
        if exit_states.get(&block_id) == Some(&state) {
            continue;
        }
        exit_states.insert(block_id, state);
        for successor in block.terminator().successors() {
            if !queued[successor.as_index()] {
                queued[successor.as_index()] = true;
                worklist.push(Reverse((
                    reverse_postorder[successor.as_index()],
                    successor.as_index(),
                )));
            }
        }
    }

    Run {
        entry_states,
        exit_states,
        interner,
    }
}

/// States `0 <= cursor` for each induction whose cursor a join merged, where the range is ascending.
///
/// Below its construction, `start <= end ⇒ start <= cursor` holds: every step keeps it (see
/// [`unproved_steps`]). Only a join makes the cursor a value no earlier fact relates to.
fn state_cursor_invariants(
    state: &mut State,
    block: BlockId,
    context: &Context<'_>,
    dominance: &Dominance,
    interner: &mut Interner,
) {
    for (root, induction) in context.inductions {
        let construction = induction.construction.as_index();
        if construction == block.as_index() || !dominance.dominates(construction, block.as_index())
        {
            continue;
        }
        let iterator = interner.place_root(*root);
        let cursor = interner.place_field(iterator, induction.layout.next);
        let symbol = state.symbol_of(cursor, interner);
        if symbol != interner.symbol(Symbol::Stored(cursor, DefSite::Join(block))) {
            continue;
        }
        let range = interner.place_field(iterator, induction.layout.range);
        let end = interner.place_field(range, induction.layout.end);
        let end = state.place_affine(end, interner);
        let ascending = Predicate::between(
            &Affine::constant(induction.start),
            Comparison::LessOrEqual,
            &end,
        );
        let above_zero = Predicate::between(
            &Affine::constant(0),
            Comparison::LessOrEqual,
            &Affine::symbol(symbol),
        );
        if let (Some(ascending), Some(above_zero)) = (ascending, above_zero)
            && state.implies(&ascending)
        {
            state.assume(above_zero);
        }
    }
}

/// Seeds the structural register-to-place map shared by local recognition and the fixed point.
///
/// MIR registers are SSA. An `alloca` or `runtime_alloc` result always names its root and a
/// `subfield` result always names the same child of its base, independently of which flow state
/// reaches a use. Resolve those identities once rather than rediscovering and carrying them through
/// every state. The small fixed point only accommodates block order not being dominance order;
/// each successful round binds at least one of the finite register set.
fn seed_register_places(func: &Function, escaped: &FxHashSet<Root>, interner: &mut Interner) {
    for block in func.blocks() {
        for operation in func.block(block).operations() {
            if !matches!(
                operation.kind,
                OperationKind::Alloca { .. } | OperationKind::RuntimeAlloc { .. }
            ) {
                continue;
            }
            let Some(register) = operation.result_id() else {
                continue;
            };
            let root = Root::Alloca(register);
            if !escaped.contains(&root) {
                let place = interner.place_root(root);
                interner.bind_register_place(register, place);
            }
        }
    }

    loop {
        let mut changed = false;
        for block in func.blocks() {
            for operation in func.block(block).operations() {
                let OperationKind::Subfield { .. } = operation.kind else {
                    continue;
                };
                let Some(register) = operation.result_id() else {
                    continue;
                };
                if interner.register_place(register).is_some() {
                    continue;
                }
                let base = match &operation.operands[0] {
                    mir::Value::Register(register) => interner.register_place(*register),
                    mir::Value::Parameter(parameter) => {
                        Some(interner.place_root(Root::Parameter(*parameter)))
                    }
                    _ => None,
                };
                let (Some(base), Some(field)) = (base, field_index(&operation.operands[1], func))
                else {
                    continue;
                };
                if escaped.contains(&interner.places().root_of(base)) {
                    continue;
                }
                let place = interner.place_field(base, field);
                changed |= interner.bind_register_place(register, place);
            }
        }
        if !changed {
            break;
        }
    }
}

/// Iterator storage whose cursor provably starts at a non-negative constant and changes by one.
///
/// This is the *constant-start, unit-step* form and nothing more general. What recognition
/// establishes is the loop invariant `0 <= cursor` for the ascending case, which no per-edge fact
/// can give: the cursor is a different value on every iteration, and joining the entry value with
/// the stepped one loses the relation that both are non-negative. The separate `start <= end`
/// proof selects that ascending case in [`yield_fact`]. Recognizing the shape of the whole loop is
/// what replaces that inference, and it is why the plan calls for this before any interval or
/// scalar-evolution machinery.
///
/// A root qualifies when all of the following hold, each of which is a way the invariant could
/// otherwise be broken:
///
/// - it is `alloca` storage for a range iterator, and does not escape;
/// - every write into it other than a step is in **one** block — the construction;
/// - that block dominates every step, so the construction always precedes them;
/// - that block is not reachable from any step, so it is outside the loop and cannot re-run;
/// - after it, the cursor and the range's lower bound are the same non-negative constant.
///
/// The start is kept rather than just checked because proving the range ascending requires
/// `start <= end`: `1..n` counts down when `n` is zero, exactly as `0..n` does when `n` is
/// negative. Recognition proves the cursor starts non-negative; [`yield_fact`] separately asks the
/// flow state for that ordering before attaching ascending bounds to a yielded cursor.
///
/// The single-block restriction is what the desugared `for` produces and is deliberately not
/// generalized: a construction spread over blocks would need each one checked against the rest.
fn recognize(
    context: &Context<'_>,
    register_places: &PlaceBindings,
    interner: &mut Interner,
) -> Recognized {
    let func = context.func;
    let candidates: Vec<(Root, RangeLayout, bool)> = func
        .blocks()
        .flat_map(|block| func.block(block).operations())
        .filter_map(|operation| {
            let OperationKind::Alloca { ty } = &operation.kind else {
                return None;
            };
            let root = Root::Alloca(operation.result_id()?);
            if context.escaped.contains(&root) {
                return None;
            }
            let (kind, layout) = context.semantics.known.range_iterator(*ty)?;
            Some((root, layout, kind == KnownCallee::RangeInclusiveNext))
        })
        .collect();
    if candidates.is_empty() {
        return Recognized::default();
    }

    let successor_lists: Vec<Vec<usize>> = func
        .blocks()
        .map(|block| {
            func.block(block)
                .terminator()
                .successors()
                .map(|target| target.as_index())
                .collect()
        })
        .collect();
    let dominance = Dominance::of(&successor_lists, func.entry().as_index());

    let mut recognized = Recognized::default();
    for (root, layout, inclusive) in candidates {
        let iterator = interner.place_root(root);
        let cursor = interner.place_field(iterator, layout.next);
        let Some((construction, steps)) = construction_block(
            context,
            register_places,
            root,
            cursor,
            interner,
            &dominance,
            &successor_lists,
        ) else {
            continue;
        };
        // The shape above proves this one block contains every non-step write to the iterator. A
        // local interpretation is consequently sufficient to inspect its initializer when the
        // values are constructed there. Values arriving through predecessors remain unknown and
        // conservatively refuse recognition.
        let mut state = State::default();
        let block = func.block(construction);
        for (index, operation) in block.operations().iter().enumerate() {
            transfer(
                operation,
                site(construction, index),
                context,
                interner,
                &mut state,
            );
        }
        if let TerminatorKind::Invoke { operation, .. } = &block.terminator().kind {
            transfer(
                operation,
                site(construction, block.operations().len()),
                context,
                interner,
                &mut state,
            );
        }
        let range = interner.place_field(iterator, layout.range);
        let lower = interner.place_field(range, layout.start);
        let constant =
            |place, interner: &mut Interner| state.place_affine(place, interner).as_constant();
        let (Some(cursor), Some(lower)) = (constant(cursor, interner), constant(lower, interner))
        else {
            continue;
        };
        if cursor == lower && cursor >= 0 {
            recognized.inductions.insert(
                root,
                Induction {
                    layout,
                    inclusive,
                    start: cursor,
                    construction,
                },
            );
            recognized
                .steps
                .extend(steps.into_iter().map(|site| (root, site)));
        }
    }
    if !recognized.inductions.is_empty() {
        recognized.dominance = Some(dominance);
    }
    recognized
}

/// What [`recognize`] found: the inductions, the inlined steps each one still owes a proof for,
/// and the dominance their invariant is stated under.
#[derive(Default)]
struct Recognized {
    inductions: FxHashMap<Root, Induction>,
    steps: Vec<(Root, OperationSite)>,
    dominance: Option<Dominance>,
}

/// The one block that writes an iterator outside its steps, if the shape [`recognize`] requires
/// holds, and the inlined steps among those.
///
/// A step is a call to the iterator's `next`, or what inlining leaves of one: a write of the cursor
/// alone, outside the construction, which [`unproved_steps`] later checks.
fn construction_block(
    context: &Context<'_>,
    register_places: &PlaceBindings,
    root: Root,
    cursor: PlaceId,
    interner: &Interner,
    dominance: &Dominance,
    successor_lists: &[Vec<usize>],
) -> Option<(BlockId, Vec<OperationSite>)> {
    let func = context.func;
    let mut construction: Option<BlockId> = None;
    let mut calls = Vec::new();
    let mut cursor_writes = Vec::new();
    for block in func.blocks() {
        let operations = func.block(block).operations().iter();
        let invoked = match &func.block(block).terminator().kind {
            TerminatorKind::Invoke { operation, .. } => Some(operation),
            _ => None,
        };
        for (index, operation) in operations.chain(invoked).enumerate() {
            if !writes_into(operation, root, register_places) {
                continue;
            }
            if context.semantics.of(operation).is_some_and(|known| {
                matches!(
                    known,
                    KnownCallee::RangeNext | KnownCallee::RangeInclusiveNext
                )
            }) {
                calls.push(block);
            } else if writes_only(operation, cursor, root, register_places, interner) {
                cursor_writes.push(OperationSite {
                    block,
                    index: OperationIndex::from_index(index),
                });
            } else {
                match construction {
                    Some(existing) if existing != block => return None,
                    _ => construction = Some(block),
                }
            }
        }
    }

    // A cursor write in the construction block is part of the construction, which the local
    // interpretation in `recognize` reads.
    let construction = construction?;
    cursor_writes.retain(|site| site.block != construction);
    let steps: Vec<BlockId> = calls
        .into_iter()
        .chain(cursor_writes.iter().map(|site| site.block))
        .collect();
    if steps.is_empty() {
        return None;
    }
    let reaches_construction = reachable_from(successor_lists, &steps);
    steps
        .iter()
        .all(|step| dominance.dominates(construction.as_index(), step.as_index()))
        .then_some(())?;
    (!reaches_construction.contains(&construction.as_index()))
        .then_some((construction, cursor_writes))
}

/// Whether `operation` writes `place` and nothing else inside `root`.
fn writes_only(
    operation: &Operation,
    place: PlaceId,
    root: Root,
    register_places: &PlaceBindings,
    interner: &Interner,
) -> bool {
    let names = |operand: &mir::Value| matches!(operand, mir::Value::Register(id) if interner.register_place(*id) == Some(place));
    let rooted = |operand: &mir::Value| matches!(operand, mir::Value::Register(id) if register_places.root_of_register(*id) == Some(root));
    match &operation.kind {
        OperationKind::Store => names(&operation.operands[1]),
        OperationKind::Memcpy | OperationKind::Move | OperationKind::MoveBytes { .. } => {
            names(&operation.operands[1]) && !operation.operands.iter().skip(2).any(rooted)
        }
        OperationKind::Call { ty, .. } => {
            call_operands(&operation.operands, ty).is_some_and(|call| {
                names(call.result)
                    && !call.arguments.iter().any(|(operand, convention)| {
                        matches!(convention, ArgConvention::MutableRef) && rooted(operand)
                    })
            })
        }
        _ => false,
    }
}

/// The blocks reachable from any of `from`, following its own edges.
fn reachable_from(successor_lists: &[Vec<usize>], from: &[BlockId]) -> FxHashSet<usize> {
    let mut seen = FxHashSet::default();
    let mut worklist: Vec<usize> = from.iter().map(|block| block.as_index()).collect();
    while let Some(block) = worklist.pop() {
        for successor in &successor_lists[block] {
            if seen.insert(*successor) {
                worklist.push(*successor);
            }
        }
    }
    seen
}

/// Whether an operation writes anywhere inside `root`.
///
/// Conservative in the direction that matters: an operation whose effect on the root this cannot
/// classify counts as a write, so an unrecognized mutation disqualifies the loop rather than being
/// silently tolerated.
fn writes_into(operation: &Operation, root: Root, register_places: &PlaceBindings) -> bool {
    let rooted = |operand: &mir::Value| match operand {
        mir::Value::Register(id) => register_places.root_of_register(*id) == Some(root),
        mir::Value::Parameter(id) => root == Root::Parameter(*id),
        _ => false,
    };
    match &operation.kind {
        OperationKind::Alloca { .. }
        | OperationKind::AllocaPlace { .. }
        | OperationKind::RuntimeAlloc { .. } => false,
        // Reads: the place is borrowed and left as it was.
        OperationKind::Load
        | OperationKind::CompareEqual
        | OperationKind::ExtractTag
        | OperationKind::ExtractPayloadIndirection
        | OperationKind::IsInitialized
        | OperationKind::Subfield { .. }
        | OperationKind::AddressOffset { .. }
        | OperationKind::AddressOffsetPlace { .. }
        | OperationKind::DictEntry { .. } => false,
        OperationKind::Store => rooted(&operation.operands[1]),
        OperationKind::Memcpy | OperationKind::Move | OperationKind::MoveBytes { .. } => {
            rooted(&operation.operands[1]) || operation.operands.iter().skip(2).any(rooted)
        }
        OperationKind::Clear
        | OperationKind::Drop { .. }
        | OperationKind::DropInitialized { .. } => rooted(&operation.operands[0]),
        OperationKind::Clone { .. } => rooted(&operation.operands[1]),
        OperationKind::Call { ty, .. } => match call_operands(&operation.operands, ty) {
            Some(call) => {
                rooted(call.result)
                    || call.arguments.iter().any(|(operand, convention)| {
                        matches!(convention, ArgConvention::MutableRef) && rooted(operand)
                    })
            }
            None => operation.operands.iter().any(rooted),
        },
        _ => operation.operands.iter().any(rooted),
    }
}

/// The state reaching one successor, which is not in general the state the block left off in.
///
/// Control-flow terminators can say something their block did not.
///
/// A `condbr` arm is taken exactly when the condition holds, so the taken edge carries the predicate
/// and the other carries its negation. This is the whole reason the comparison idiom is reassembled
/// into a [`Predicate`] earlier — a boolean nobody can read says nothing about either arm. A `condbr`
/// whose two arms are the same block refines neither: the block is reached whichever way the
/// condition went.
///
/// An `InBounds` condition contributes both signed bounds on success. Failure is their disjunction;
/// it contributes one negated bound only when the other bound already holds.
///
/// A `switch_variant` carries the same fact directly on a symbolic tag edge. Its default edge
/// carries the negation of every named truth predicate.
///
/// An `invoke` of a bounds check refines its normal edge with what returning proved, which is
/// [`resolved_index_bounds`].
///
/// `None` when the edge cannot be taken: its condition contradicts what is known, or it is the
/// normal edge of a call that [diverges](Operation::diverges).
fn refine<'a>(
    state: &'a State,
    terminator: &TerminatorKind,
    successor: BlockId,
    context: &Context<'_>,
    interner: &mut Interner,
) -> Option<Cow<'a, State>> {
    // Borrowed on every path that adds nothing, which is most edges: a state is several maps, and
    // cloning one per edge per visit was pure waste.
    let assumed = match terminator {
        TerminatorKind::CondBr {
            condition,
            then_target,
            else_target,
        } => {
            if then_target == else_target {
                return Some(Cow::Borrowed(state));
            }
            match condition_fact(state, condition, interner) {
                Some(Fact::Truth(predicate)) => vec![if successor == *then_target {
                    predicate
                } else {
                    predicate.negated()
                }],
                Some(Fact::InBounds { offset, length }) => {
                    bounds_edge_predicates(state, offset, length, successor == *then_target)
                }
                Some(Fact::Implies(predicates)) if successor == *then_target => predicates,
                _ => return Some(Cow::Borrowed(state)),
            }
        }
        TerminatorKind::SwitchVariant {
            tag,
            cases,
            default,
        } => {
            let Some(scrutinee) = condition_fact(state, tag, interner) else {
                return Some(Cow::Borrowed(state));
            };
            let matching: Vec<_> = cases
                .iter()
                .filter(|(_, target)| *target == successor)
                .collect();
            if *default != successor && matching.len() == 1 {
                match variant_case_fact(&scrutinee, matching[0].0) {
                    Some(Fact::Truth(predicate)) => vec![predicate],
                    Some(Fact::Implies(predicates)) => predicates,
                    _ => return Some(Cow::Borrowed(state)),
                }
            } else if *default == successor && matching.is_empty() && !cases.is_empty() {
                let mut predicates = Vec::with_capacity(cases.len());
                for (case, _) in cases {
                    match variant_case_fact(&scrutinee, *case) {
                        Some(Fact::Truth(predicate)) => predicates.push(predicate.negated()),
                        _ => return Some(Cow::Borrowed(state)),
                    }
                }
                predicates
            } else {
                return Some(Cow::Borrowed(state));
            }
        }
        TerminatorKind::Invoke {
            operation, normal, ..
        } if successor == *normal && operation.diverges() => return None,
        TerminatorKind::Invoke {
            operation, normal, ..
        } if successor == *normal => match context.semantics.of(operation) {
            Some(KnownCallee::ArrayResolveIndex) => {
                match resolved_index_bounds(state, operation, context, interner) {
                    Some(predicates) => predicates,
                    None => return Some(Cow::Borrowed(state)),
                }
            }
            Some(KnownCallee::ArrayIndex) => {
                match checked_array_index_bounds(state, operation, context, interner) {
                    Some(predicates) => predicates,
                    None => return Some(Cow::Borrowed(state)),
                }
            }
            _ => return Some(Cow::Borrowed(state)),
        },
        _ => return Some(Cow::Borrowed(state)),
    };
    if assumed.is_empty() {
        return Some(Cow::Borrowed(state));
    }
    // An edge whose condition contradicts what is known is never taken. Nothing flows along it, so
    // a join below does not lose what the feasible edges agree on.
    if assumed
        .iter()
        .any(|predicate| state.implies(&predicate.negated()))
    {
        return None;
    }
    let mut refined = state.clone();
    for predicate in assumed {
        refined.assume(predicate);
    }
    Some(Cow::Owned(refined))
}

/// A failed range check is `offset < 0 || offset >= length`. Refine it only when
/// an already established bound rules out one side; assuming both would be unsound.
fn bounds_edge_predicates(
    state: &State,
    offset: Affine,
    length: Affine,
    success: bool,
) -> Vec<Predicate> {
    let nonnegative = Predicate::between(&Affine::constant(0), Comparison::LessOrEqual, &offset)
        .expect("an order always has an affine representation");
    let below_length = Predicate::between(&offset, Comparison::Less, &length)
        .expect("an order always has an affine representation");
    if success {
        vec![nonnegative, below_length]
    } else if state.implies(&nonnegative) {
        vec![below_length.negated()]
    } else if state.implies(&below_length) {
        vec![nonnegative.negated()]
    } else {
        Vec::new()
    }
}

/// What a bounds check proves by returning at all, for the edge along which it returned.
///
/// `array_resolve_index(index, len)` panics unless the offset it hands back lies in `0..len`, so the
/// normal edge carries exactly that. It is the one obligation an element access has, which is what
/// makes an access that survives worth as much to the accesses after it as a guard the source wrote.
///
/// Which value the bound is *about* is the whole subtlety. The callee rewrites a negative index into
/// `len + index` and leaves every other one alone, so when the index is already known non-negative
/// the offset is the index itself and the bound lands on the expression the caller wrote — where a
/// later loop over the same array can use it. Otherwise it lands on the offset, a value only the
/// check names, and says nothing about the index that produced it.
fn resolved_index_bounds(
    state: &State,
    operation: &Operation,
    context: &Context<'_>,
    interner: &mut Interner,
) -> Option<Vec<Predicate>> {
    if context.semantics.of(operation)? != KnownCallee::ArrayResolveIndex {
        return None;
    }
    let OperationKind::Call { ty, .. } = &operation.kind else {
        return None;
    };
    let call = call_operands(&operation.operands, ty)?;
    let index = argument_affine(call.arguments.first()?.0, interner, state)?;
    let len = argument_affine(call.arguments.get(1)?.0, interner, state)?;
    let zero = Affine::constant(0);
    let offset = if state.implies(&Predicate::between(&zero, Comparison::LessOrEqual, &index)?) {
        index
    } else {
        let place = tracked_place(state, call.result, context.escaped, interner)?;
        state.place_affine(place, interner)
    };
    Some(vec![
        Predicate::between(&zero, Comparison::LessOrEqual, &offset)?,
        Predicate::between(&offset, Comparison::Less, &len)?,
    ])
}

/// What a successful checked array access proves about its original index.
///
/// A negative index is legal and is normalized inside the accessor, so success alone cannot put
/// the source index in `0..len`. When the incoming state independently proves non-negativity,
/// however, the successful normal edge proves the remaining upper bound and makes a later checked
/// access usable as an unchecked offset.
fn checked_array_index_bounds(
    state: &State,
    operation: &Operation,
    context: &Context<'_>,
    interner: &mut Interner,
) -> Option<Vec<Predicate>> {
    let (index, len) = context.array_index_forms(operation, state, interner)?;
    let zero = Affine::constant(0);
    let nonnegative = Predicate::between(&zero, Comparison::LessOrEqual, &index)?;
    if !state.implies(&nonnegative) {
        return None;
    }
    Some(vec![
        nonnegative,
        Predicate::between(&index, Comparison::Less, &len)?,
    ])
}

/// What is known about the value a terminator branches on.
fn condition_fact(state: &State, condition: &mir::Value, interner: &mut Interner) -> Option<Fact> {
    match condition {
        mir::Value::Register(id) => {
            let symbol = interner.symbol(Symbol::Register(*id));
            state.fact(symbol).cloned()
        }
        _ => {
            let place = state.place_of(condition, interner)?;
            let symbol = state.symbol_of(place, interner);
            state.fact(symbol).cloned()
        }
    }
}

/// The definition site of the operation at `index` in `block`.
fn site(block: BlockId, index: usize) -> DefSite {
    DefSite::Operation(OperationSite {
        block,
        index: OperationIndex::from_index(index),
    })
}

/// Joins two edges into a block, giving every place the two disagree about a definition of the
/// block itself.
///
/// The join site has to be named, or a place written differently on two paths would keep whichever
/// predecessor was walked last and facts from one arm would leak into the other.
fn rejoin(existing: &State, incoming: &State, block: BlockId, interner: &mut Interner) -> State {
    let mut current = FxHashMap::default();
    for (place, symbol) in &existing.current {
        let symbol = match incoming.current.get(place) {
            Some(incoming) if incoming == symbol => *symbol,
            _ => interner.symbol(Symbol::Stored(*place, DefSite::Join(block))),
        };
        current.insert(*place, symbol);
    }
    // A place present only on the incoming edge disagrees just as one present only on the existing
    // edge does. Visit it once; chaining both key sets made every place present on both sides take
    // the disagreement path twice.
    for place in incoming.current.keys() {
        if existing.current.contains_key(place) {
            continue;
        }
        let symbol = interner.symbol(Symbol::Stored(*place, DefSite::Join(block)));
        current.insert(*place, symbol);
    }
    let (facts, known) = existing.common_facts_and_predicates(incoming);
    State {
        current,
        facts,
        known,
    }
}

/// The slot an operand names, when the escape scan left it trackable.
fn tracked_place(
    state: &State,
    operand: &mir::Value,
    escaped: &FxHashSet<Root>,
    interner: &mut Interner,
) -> Option<PlaceId> {
    let place = state.place_of(operand, interner)?;
    (!escaped.contains(&interner.places().root_of(place))).then_some(place)
}

/// The transfer function for one operation.
///
/// `def` names the value any place this operation writes will hold afterwards.
fn transfer(
    operation: &Operation,
    def: DefSite,
    context: &Context<'_>,
    interner: &mut Interner,
    state: &mut State,
) {
    let Context {
        func,
        semantics,
        escaped,
        types,
        inductions,
    } = context;
    match &operation.kind {
        // `alloca_place` is deliberately absent: the escape scan does not register its result as a
        // root, so nothing could ever mark it escaped, and tracking a place the scan cannot escape
        // would be trusting writes it never saw. Its slots stay unnamed until the scan roots them.
        OperationKind::Alloca { .. } | OperationKind::RuntimeAlloc { .. } => {
            let Some(result) = operation.result_id() else {
                return;
            };
            let root = Root::Alloca(result);
            if escaped.contains(&root) {
                return;
            }
            let place = interner.place_root(root);
            interner.bind_register_place(result, place);
            state.define(place, def, interner, None);
        }
        OperationKind::RuntimeDealloc => {
            if let Some(place) = tracked_place(state, &operation.operands[0], escaped, interner) {
                state.forget(place, interner);
            }
        }
        OperationKind::Store => {
            let Some(place) = tracked_place(state, &operation.operands[1], escaped, interner)
            else {
                return;
            };
            let fact = value_fact(&operation.operands[0], func, interner, state);
            state.define(place, def, interner, fact);
        }
        OperationKind::BuildArray { .. } => {
            let Some((destination, elements)) = operation.operands.split_last() else {
                return;
            };
            let Some(array) = tracked_place(state, destination, escaped, interner) else {
                return;
            };
            // `build_array` initializes the complete high-level array value. Define the whole
            // destination first, because doing so forgets every fact about its old fields, then
            // state the one representation fact the operation determines independently of its
            // element values. Copies and moves already carry named fields with the whole value.
            state.define(array, def, interner, None);
            let len = interner.place_field(array, semantics.known.layouts().array_len);
            let count = Int::try_from(elements.len())
                .expect("a MIR operation has fewer elements than int can represent");
            state.define(
                len,
                def,
                interner,
                Some(Fact::Value(Affine::constant(count))),
            );
        }
        OperationKind::Load => {
            let Some(result) = operation.result_id() else {
                return;
            };
            let fact =
                tracked_place(state, &operation.operands[0], escaped, interner).map(|place| {
                    let symbol = state.symbol_of(place, interner);
                    // A load with nothing known still yields the *same* value the slot holds, which is
                    // what lets two loads of an unwritten slot compare equal.
                    state
                        .fact(symbol)
                        .cloned()
                        .unwrap_or_else(|| Fact::Value(state.place_affine(place, interner)))
                });
            let symbol = interner.symbol(Symbol::Register(result));
            state.set_fact(symbol, fact);
        }
        OperationKind::Subfield { .. } => {
            let Some(result) = operation.result_id() else {
                return;
            };
            if let (Some(base), Some(index)) = (
                tracked_place(state, &operation.operands[0], escaped, interner),
                field_index(&operation.operands[1], func),
            ) {
                // An array's length is never negative, and no MIR operation says so. Without it a
                // `for i in 0..len(a)` loop cannot even be shown to count *upwards*, because a
                // range whose end is below its start counts down.
                let field = interner.place_field(base, index);
                if interner.places().is_root(base)
                    && index == semantics.known.layouts().array_len
                    && types
                        .of(interner.places().root_of(base))
                        .is_some_and(|ty| semantics.known.is_array(ty))
                {
                    let length = state.place_affine(field, interner);
                    if let Some(predicate) =
                        Predicate::between(&Affine::constant(0), Comparison::LessOrEqual, &length)
                    {
                        state.assume(predicate);
                    }
                }
                interner.bind_register_place(result, field);
            }
        }
        OperationKind::AddressOffset { .. } | OperationKind::AddressOffsetPlace { .. } => {}
        OperationKind::Memcpy | OperationKind::Move | OperationKind::MoveBytes { .. } => {
            let source = tracked_place(state, &operation.operands[0], escaped, interner);
            let destination = tracked_place(state, &operation.operands[1], escaped, interner);
            // Do not redefine the value or its fields for an identity transfer, including aliases
            // represented by different projection registers.
            if source.is_some() && source == destination {
                return;
            }
            if let Some(destination) = destination {
                // The fields travel too, and separately from the whole: a struct's own fact says
                // nothing about its fields, and a range is built field by field and then copied
                // into its iterator in one go. Losing the fields there loses the loop's bounds.
                let contents = state.place_contents(source, interner);
                state.define_contents(destination, def, interner, contents);
            }
            // A move leaves its source holding nothing nameable; a memcpy preserves it.
            if matches!(
                operation.kind,
                OperationKind::Move | OperationKind::MoveBytes { .. }
            ) && let Some(place) = source
            {
                state.define(place, def, interner, None);
            }
        }
        OperationKind::Clear
        | OperationKind::Drop { .. }
        | OperationKind::DropInitialized { .. } => {
            if let Some(place) = tracked_place(state, &operation.operands[0], escaped, interner) {
                state.define(place, def, interner, None);
            }
        }
        OperationKind::Replace => {
            let source = tracked_place(state, &operation.operands[0], escaped, interner);
            let destination = tracked_place(state, &operation.operands[1], escaped, interner);
            let new_value = state.place_contents(source, interner);
            let old_value = state.place_contents(destination, interner);
            if let Some(place) = destination {
                state.define_contents(place, def, interner, new_value);
            }
            if let Some(place) = source {
                state.define_contents(place, def, interner, old_value);
            }
        }
        OperationKind::ExtractTag => {
            let Some(result) = operation.result_id() else {
                return;
            };
            // An `Ordering` has no payload, so its tag *is* the comparison it stands for.
            let fact = tracked_place(state, &operation.operands[0], escaped, interner)
                .map(|place| state.symbol_of(place, interner))
                .and_then(|symbol| state.fact(symbol).cloned())
                .filter(|fact| matches!(fact, Fact::Ordering { .. } | Fact::Yield { .. }));
            let symbol = interner.symbol(Symbol::Register(result));
            state.set_fact(symbol, fact);
        }
        OperationKind::CompareEqual => {
            let Some(result) = operation.result_id() else {
                return;
            };
            let fact = comparison_fact(operation, func, escaped, interner, state);
            let symbol = interner.symbol(Symbol::Register(result));
            state.set_fact(symbol, fact);
        }
        OperationKind::Call { ty, .. } => {
            let Some(call) = call_operands(&operation.operands, ty) else {
                return;
            };
            let known = semantics.of(operation);
            // The cursor's symbol has to be taken before the step redefines it: the value the
            // option yields is what the iterator held on the way *in*.
            let cursor = known
                .filter(|known| {
                    matches!(
                        known,
                        KnownCallee::RangeNext | KnownCallee::RangeInclusiveNext
                    )
                })
                .and_then(|_| iterator_place(&call.arguments, state, interner))
                .filter(|place| inductions.contains_key(&interner.places().root_of(*place)))
                .map(|place| {
                    let induction = inductions[&interner.places().root_of(place)];
                    let cursor = interner.place_field(place, induction.layout.next);
                    state.symbol_of(cursor, interner)
                });
            // Whatever a callee may write through is no longer the value it was, whether or not the
            // callee's meaning is known: knowing what a call computes says nothing about the slots
            // it wrote on the way.
            for (operand, convention) in &call.arguments {
                if matches!(convention, ArgConvention::MutableRef)
                    && let Some(place) = tracked_place(state, operand, escaped, interner)
                {
                    // A range step writes the cursor and nothing else, so forgetting the whole
                    // iterator would throw away the very bounds the loop is being read for. This is
                    // the precision a resolved callee buys: an unknown one still loses everything.
                    match known {
                        // These addressors receive a mutable receiver so the place they return can
                        // be written through; computing that place does not itself mutate the
                        // array. Forgetting the receiver here would discard its length immediately
                        // before the successful-access edge tries to record the bound it proved.
                        Some(KnownCallee::ArrayIndex | KnownCallee::ArrayOffsetUnchecked) => {}
                        _ => match stepped_cursor(known, place, types, semantics, interner) {
                            Some(cursor) => state.define(cursor, def, interner, None),
                            None => state.define(place, def, interner, None),
                        },
                    }
                }
            }
            let fact = known.and_then(|known| {
                result_fact(
                    known,
                    &call.arguments,
                    escaped,
                    semantics.known.layouts(),
                    interner,
                    state,
                )
            });
            let fact = fact.or_else(|| {
                yield_fact(known?, &call.arguments, inductions, cursor, interner, state)
            });
            if let Some(place) = tracked_place(state, call.result, escaped, interner) {
                state.define(place, def, interner, fact);
            }
        }
        OperationKind::Clone { .. } => {
            if let Some(place) = tracked_place(state, &operation.operands[1], escaped, interner) {
                state.define(place, def, interner, None);
            }
        }
        _ => {
            // Not modelled: the escape scan has escaped every place this operation touches, so
            // there is nothing left to invalidate. A result register holds an unnamed value.
            if let Some(result) = operation.result_id() {
                let symbol = interner.symbol(Symbol::Register(result));
                state.set_fact(symbol, None);
            }
        }
    }
}

/// What a known call leaves in its result slot.
fn result_fact(
    known: KnownCallee,
    arguments: &[(&mir::Value, ArgConvention)],
    escaped: &FxHashSet<Root>,
    layouts: &Layouts,
    interner: &mut Interner,
    state: &State,
) -> Option<Fact> {
    let operand = |index: usize| arguments.get(index).map(|(operand, _)| *operand);
    let affine = |index: usize, interner: &mut Interner| -> Option<Affine> {
        argument_affine(operand(index)?, interner, state)
    };
    match known {
        KnownCallee::IntAdd => {
            let left = affine(0, interner)?;
            let right = affine(1, interner)?;
            left.add(&right).map(Fact::Value)
        }
        KnownCallee::IntSub => {
            let left = affine(0, interner)?;
            let right = affine(1, interner)?;
            left.sub(&right).map(Fact::Value)
        }
        KnownCallee::IntMul => {
            let left = affine(0, interner)?;
            let right = affine(1, interner)?;
            left.mul(&right).map(Fact::Value)
        }
        KnownCallee::IntNeg => Some(Fact::Value(affine(0, interner)?.scale(-1))),
        // The conversion every integer literal is desugared into, and at `int` it converts nothing:
        // the result is the argument, so it must not become an unrelated symbol.
        KnownCallee::IntFromInt => Some(Fact::Value(affine(0, interner)?)),
        KnownCallee::ArrayOffsetInBounds => Some(Fact::InBounds {
            offset: affine(0, interner)?,
            length: affine(1, interner)?,
        }),
        KnownCallee::IntLt => Predicate::between(
            &affine(0, interner)?,
            Comparison::Less,
            &affine(1, interner)?,
        )
        .map(Fact::Truth),
        KnownCallee::IntLe => Predicate::between(
            &affine(0, interner)?,
            Comparison::LessOrEqual,
            &affine(1, interner)?,
        )
        .map(Fact::Truth),
        KnownCallee::IntGt => Predicate::between(
            &affine(1, interner)?,
            Comparison::Less,
            &affine(0, interner)?,
        )
        .map(Fact::Truth),
        KnownCallee::IntGe => Predicate::between(
            &affine(1, interner)?,
            Comparison::LessOrEqual,
            &affine(0, interner)?,
        )
        .map(Fact::Truth),
        KnownCallee::IntEq => Predicate::between(
            &affine(0, interner)?,
            Comparison::Equal,
            &affine(1, interner)?,
        )
        .map(Fact::Truth),
        KnownCallee::IntCmp => Some(Fact::Ordering {
            left: affine(0, interner)?,
            right: affine(1, interner)?,
        }),
        // `array_len` *is* the field read, and saying so is what lets a bound and a check agree.
        // They reach the length by different routes — a specialized body reads `a.len` directly to
        // build a range and calls `array_len` inside the loop for the same quantity — and an opaque
        // result makes those two unrelated symbols, which is every bound the loop was analysed for.
        KnownCallee::ArrayLen => {
            let array = tracked_place(state, operand(0)?, escaped, interner)?;
            let len = interner.place_field(array, layouts.array_len);
            Some(Fact::Value(state.place_affine(len, interner)))
        }
        // This domain carries affine integers only. Other known callees conservatively contribute
        // no fact; their result remains nameable through the fresh symbol assigned by the caller.
        _ => None,
    }
}

/// The cursor a range step writes, for a call that is one.
///
/// `None` for every other call, including one on an iterator whose induction was not recognized:
/// the layout is what makes the narrower write expressible, and it comes from the iterator's type
/// rather than from the loop's shape.
fn stepped_cursor(
    known: Option<KnownCallee>,
    place: PlaceId,
    types: &RootTypes,
    semantics: &Semantics<'_>,
    interner: &mut Interner,
) -> Option<PlaceId> {
    if !matches!(
        known?,
        KnownCallee::RangeNext | KnownCallee::RangeInclusiveNext
    ) || !interner.places().is_root(place)
    {
        return None;
    }
    let root = interner.places().root_of(place);
    let (_, layout) = semantics.known.range_iterator(types.of(root)?)?;
    Some(interner.place_field(place, layout.next))
}

/// The iterator a range step is walking.
fn iterator_place(
    arguments: &[(&mir::Value, ArgConvention)],
    state: &State,
    interner: &mut Interner,
) -> Option<PlaceId> {
    let (operand, _) = arguments
        .iter()
        .find(|(_, convention)| matches!(convention, ArgConvention::MutableRef))?;
    state.place_of(operand, interner)
}

/// What a step of a recognized range loop leaves in its result slot.
///
/// The two bounds come from different places and only one of them is a per-call fact. `cursor < end`
/// is what a step *tests* before yielding, so it holds on the `Some` path — but only ascending,
/// since a range whose end is below its start counts down and yields while `cursor > end` instead.
/// `0 <= cursor` is the loop invariant, and it is [`recognize`] rather than this that established
/// it.
fn yield_fact(
    known: KnownCallee,
    arguments: &[(&mir::Value, ArgConvention)],
    inductions: &FxHashMap<Root, Induction>,
    cursor: Option<SymbolId>,
    interner: &mut Interner,
    state: &State,
) -> Option<Fact> {
    if !matches!(
        known,
        KnownCallee::RangeNext | KnownCallee::RangeInclusiveNext
    ) {
        return None;
    }
    let cursor = cursor?;
    let iterator = iterator_place(arguments, state, interner)?;
    let induction = *inductions.get(&interner.places().root_of(iterator))?;
    let range = interner.place_field(iterator, induction.layout.range);
    let upper = interner.place_field(range, induction.layout.end);
    let end = state.place_affine(upper, interner);
    // Ascending, which is the end being at or above the start. Without it the iterator counts down
    // and every bound below is the wrong way round.
    let ascending = Predicate::between(
        &Affine::constant(induction.start),
        Comparison::LessOrEqual,
        &end,
    )?;
    if !state.implies(&ascending) {
        return None;
    }
    let value = Affine::symbol(cursor);
    let above_zero = Predicate::between(&Affine::constant(0), Comparison::LessOrEqual, &value)?;
    let below_end = Predicate::between(
        &value,
        if induction.inclusive {
            Comparison::LessOrEqual
        } else {
            Comparison::Less
        },
        &end,
    )?;
    Some(Fact::Yield {
        value: cursor,
        present_when: vec![above_zero, below_end],
    })
}

/// The affine form of a value read through a call argument.
///
/// An argument is always a place: MIR has no immediate operands at a call, so a literal reaches one
/// through a slot it was stored into, and that store is where its form was recorded.
fn argument_affine(operand: &mir::Value, interner: &mut Interner, state: &State) -> Option<Affine> {
    let place = state.place_of(operand, interner)?;
    Some(state.place_affine(place, interner))
}

/// The fact for an operand used as a materialized value.
fn value_fact(
    operand: &mir::Value,
    func: &Function,
    interner: &mut Interner,
    state: &State,
) -> Option<Fact> {
    match operand {
        mir::Value::Constant(id) => func
            .constant(*id)
            .representation
            .as_primitive_ty::<Int>()
            .map(|value| Fact::Value(Affine::constant(*value))),
        mir::Value::Register(id) => {
            let symbol = interner.symbol(Symbol::Register(*id));
            state.fact(symbol).cloned()
        }
        _ => None,
    }
}

/// The truth a `comp_eq` against an `Ordering` tag establishes.
fn comparison_fact(
    operation: &Operation,
    func: &Function,
    escaped: &FxHashSet<Root>,
    interner: &mut Interner,
    state: &State,
) -> Option<Fact> {
    let scrutinee = match state.place_of(&operation.operands[0], interner) {
        Some(place) if !escaped.contains(&interner.places().root_of(place)) => {
            let symbol = state.symbol_of(place, interner);
            state.fact(symbol).cloned()
        }
        Some(_) => None,
        None => value_fact(&operation.operands[0], func, interner, state),
    }?;
    let mir::Value::Pattern(pattern) = &operation.operands[1] else {
        return None;
    };
    let tag = pattern.as_variant_tag()?;
    variant_case_fact(&scrutinee, *tag)
}

/// The fact established by selecting one symbolic case of a variant-like semantic value.
fn variant_case_fact(scrutinee: &Fact, tag: Ustr) -> Option<Fact> {
    match scrutinee {
        Fact::Ordering { left, right } => {
            let predicate = match tag.as_str() {
                "Less" => Predicate::between(left, Comparison::Less, right)?,
                "Greater" => Predicate::between(right, Comparison::Less, left)?,
                "Equal" => Predicate::between(left, Comparison::Equal, right)?,
                _ => return None,
            };
            Some(Fact::Truth(predicate))
        }
        // One direction only: the payload is in range when the option is `Some`, and a `None`
        // says nothing about a value that is not there.
        Fact::Yield { present_when, .. } if tag.as_str() == "Some" => {
            Some(Fact::Implies(present_when.clone()))
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        CompilerSession, ExecutionTarget, MirOptimization,
        module::{ModuleId, Path},
    };

    #[test]
    fn self_transfers_preserve_scalar_and_field_facts() {
        use crate::{
            Location,
            hir::value::LiteralValue,
            mir::{builder::FunctionBuilder, pass::dataflow, terminator::Terminator},
            std::math::int_type,
        };
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        let ty = Type::tuple([int_type()]);
        for whole in [false, true] {
            for transfer in [
                OperationKind::Memcpy,
                OperationKind::Move,
                OperationKind::MoveBytes {
                    ty: if whole { ty } else { int_type() },
                },
            ] {
                let mut builder = FunctionBuilder::new("self_transfer".into(), Default::default());
                let block = builder.add_block();
                let root = builder
                    .append_operation(block, Operation::alloca(span, ty))
                    .unwrap();
                let zero = builder.add_constant(int_type(), LiteralValue::new_native(0isize), &env);
                let mut project = || {
                    builder
                        .append_operation(
                            block,
                            Operation::product_subfield(
                                span,
                                root.clone(),
                                mir::Value::Constant(zero),
                                int_type(),
                                ty,
                                [],
                            ),
                        )
                        .unwrap()
                };
                let field = project();
                let alias = project();
                let value =
                    builder.add_constant(int_type(), LiteralValue::new_native(42isize), &env);
                builder.append_operation(
                    block,
                    Operation::store(span, mir::Value::Constant(value), field.clone()),
                );
                let (source, destination) = if whole {
                    (root.clone(), root)
                } else {
                    (field.clone(), alias)
                };
                let operation = match transfer {
                    OperationKind::Memcpy => Operation::memcpy(span, source, destination),
                    OperationKind::Move => Operation::move_value(span, source, destination),
                    OperationKind::MoveBytes { ty } => {
                        let size = builder.add_constant(
                            int_type(),
                            LiteralValue::new_native(size_of::<isize>() as isize),
                            &env,
                        );
                        Operation::move_bytes(
                            span,
                            ty,
                            source,
                            destination,
                            mir::Value::Constant(size),
                        )
                    }
                    _ => unreachable!(),
                };
                builder.append_operation(block, operation);
                let loaded = builder
                    .append_operation(block, Operation::load(span, field.clone()))
                    .unwrap();
                builder.set_terminator(block, Terminator::ret(span));
                let func = builder.finish(env);

                // The same fixture guards both analyses: scalar aliases must stay initialized,
                // and moving an aggregate onto itself must not erase facts about its fields.
                let constants = dataflow::analyze(&func, env);
                let mut state = constants.entry_state(block);
                for operation in func.block(block).operations() {
                    constants.step(&func, env, operation, &mut state);
                }
                assert_eq!(
                    state.place(constants.place_of(&field).unwrap()),
                    dataflow::Fact::Known(dataflow::Const::literal(LiteralValue::new_native(
                        42isize
                    )))
                );

                let mut relations = analyze(&func, session.known_callees(), &|_| None);
                let state = relations.exit_state(block).unwrap().clone();
                let mir::Value::Register(register) = loaded else {
                    unreachable!()
                };
                let symbol = relations.interner.symbol(Symbol::Register(register));
                assert_eq!(state.fact(symbol), Some(&Fact::Value(Affine::constant(42))));
            }
        }
    }

    #[test]
    fn replace_preserves_field_relations_on_both_sides() {
        use crate::{
            Location,
            hir::value::LiteralValue,
            mir::{builder::FunctionBuilder, terminator::Terminator},
            std::math::int_type,
        };
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        let ty = Type::tuple([int_type(), int_type()]);
        let mut builder = FunctionBuilder::new("replace_fields".into(), Default::default());
        let block = builder.add_block();
        let mut places = Vec::new();
        let mut fields = Vec::new();
        for base in [10isize, 20] {
            let place = builder
                .append_operation(block, Operation::alloca(span, ty))
                .unwrap();
            for index in 0..2isize {
                let offset =
                    builder.add_constant(int_type(), LiteralValue::new_native(index), &env);
                let field = builder
                    .append_operation(
                        block,
                        Operation::product_subfield(
                            span,
                            place.clone(),
                            mir::Value::Constant(offset),
                            int_type(),
                            ty,
                            [],
                        ),
                    )
                    .unwrap();
                let value =
                    builder.add_constant(int_type(), LiteralValue::new_native(base + index), &env);
                builder.append_operation(
                    block,
                    Operation::store(span, mir::Value::Constant(value), field.clone()),
                );
                fields.push(field);
            }
            places.push(place);
        }
        builder.append_operation(
            block,
            Operation::replace(span, places[0].clone(), places[1].clone(), None),
        );
        let loaded: Vec<_> = fields
            .into_iter()
            .map(|field| {
                builder
                    .append_operation(block, Operation::load(span, field))
                    .unwrap()
            })
            .collect();
        builder.set_terminator(block, Terminator::ret(span));
        let func = builder.finish(env);
        let mut analysis = analyze(&func, session.known_callees(), &|_| None);
        let state = analysis.exit_state(block).unwrap().clone();
        for (loaded, expected) in loaded.into_iter().zip([20, 21, 10, 11]) {
            let mir::Value::Register(register) = loaded else {
                unreachable!()
            };
            let symbol = analysis.interner.symbol(Symbol::Register(register));
            assert_eq!(
                state.fact(symbol),
                Some(&Fact::Value(Affine::constant(expected)))
            );
        }
    }

    /// Analyses one function of a compiled module and hands the result to `check`.
    ///
    /// **Optimized MIR, not raw.** In raw MIR a trait method is a `dict_entry` dispatch, so `a + b`
    /// has no direct callee and none of the arithmetic below is visible at all; folding and
    /// devirtualization are what make it so. Every fixture takes its inputs as parameters, so
    /// nothing folds away and what remains to observe is the relation.
    fn with_analysis(
        src: &str,
        name: &str,
        check: impl FnOnce(&Function, &mut Analysis, &KnownCallees),
    ) {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let module_id: ModuleId = session
            .compile_for(ExecutionTarget::Mir, src, "test", Path::single_str("test"))
            .expect("the test source compiles")
            .module_id;
        session.prepare_execution_target(ExecutionTarget::Mir, module_id);
        let known = session.known_callees();
        let artifacts = session
            .mir_artifacts_for(module_id, MirOptimization::Enabled)
            .expect("optimized artifacts were just built");
        let function = artifacts
            .bodies()
            .iter()
            .flatten()
            .find(|body| body.name.as_str() == name)
            .expect("the function was declared");
        let mut analysis = analyze(function, known, &|_| None);
        check(function, &mut analysis, known);
    }

    /// Every fact the final state holds, so that a test can look for one without knowing which
    /// symbol carries it.
    fn facts(function: &Function, analysis: &Analysis) -> Vec<Fact> {
        function
            .blocks()
            .filter_map(|block| analysis.exit_state(block))
            .flat_map(|state| state.facts.values().cloned())
            .collect()
    }

    /// The relation the whole analysis exists to produce: a value one more than another, stated
    /// against the other rather than against the slot it came from.
    #[test]
    fn an_increment_relates_its_result_to_its_input() {
        with_analysis(
            "fn step(i: int) -> int { i + 1 }",
            "step",
            |function, analysis, _| {
                let increments = facts(function, analysis)
                    .into_iter()
                    .filter(|fact| match fact {
                        Fact::Value(affine) => affine.constant == 1 && affine.terms().len() == 1,
                        _ => false,
                    })
                    .count();
                assert!(
                    increments > 0,
                    "`i + 1` must be recorded as one more than the symbol for `i`"
                );
            },
        );
    }

    /// A comparison must survive the call producing an `Ordering`, tag extraction and semantic
    /// switch, and arrive on the selected edge as one predicate.
    #[test]
    fn a_comparison_becomes_a_predicate_between_its_sides() {
        with_analysis(
            "fn below(i: int, n: int) -> int { if i < n { 1 } else { 0 } }",
            "below",
            |function, analysis, _| {
                let predicates: Vec<_> = function
                    .blocks()
                    .filter_map(|block| analysis.entry_state(block))
                    .flat_map(State::known)
                    .cloned()
                    .collect();
                assert!(
                    predicates
                        .iter()
                        .any(|predicate| predicate.comparison == Comparison::Less
                            && predicate.left.as_symbol().is_some()
                            && predicate.right.as_symbol().is_some()),
                    "`i < n` must become a predicate between `i` and `n`, got {predicates:?}"
                );
            },
        );
    }

    /// A callee read raw, as within a recursive component, still reaches its branch as
    /// a native `compare_int`. Its semantic ordering must carry the operand relation.
    #[test]
    fn a_native_comparison_keeps_its_operand_relation() {
        use ustr::ustr;

        use crate::{
            Location,
            containers::b,
            hir::value::LiteralValue,
            mir::{ParameterKind, builder::FunctionBuilder, terminator::Terminator},
            std::{STD_MODULE_ID, math::int_type, ordering::ordering_type},
            types::r#type::CallImplType,
        };
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        let std = session.expect_fresh_module(STD_MODULE_ID);
        let std_call = |name: &str, operands: Vec<mir::Value>| {
            let local = std.get_local_function_id(ustr(name)).unwrap();
            let definition = &std.get_function_by_id(local).unwrap().definition;
            Operation::call(
                span,
                mir::Value::Function(FunctionId::new(STD_MODULE_ID, local)),
                operands,
                CallImplType::value(definition.ty_scheme.ty.clone()),
            )
        };

        let mut builder = FunctionBuilder::new("below".into(), Default::default());
        let left = builder.add_parameter(int_type(), ParameterKind::Parameter(ArgConvention::Let));
        let right = builder.add_parameter(int_type(), ParameterKind::Parameter(ArgConvention::Let));
        let entry = builder.add_block();
        let less = builder.add_block();
        let other = builder.add_block();
        let ordering = builder
            .append_operation(entry, Operation::alloca(span, ordering_type()))
            .unwrap();
        builder.append_operation(
            entry,
            std_call(
                "compare_int",
                vec![
                    mir::Value::Parameter(left),
                    mir::Value::Parameter(right),
                    ordering.clone(),
                ],
            ),
        );
        let tag = builder
            .append_operation(entry, Operation::extract_tag(span, ordering))
            .unwrap();
        let test = builder
            .append_operation(
                entry,
                Operation::compare_eq(
                    span,
                    tag,
                    mir::Value::Pattern(b(LiteralValue::new_variant_tag(ustr("Less")))),
                ),
            )
            .unwrap();
        builder.set_terminator(entry, Terminator::cond_br(span, test, less, other));
        builder.set_terminator(less, Terminator::ret(span));
        builder.set_terminator(other, Terminator::ret(span));
        let function = builder.finish(env);

        let analysis = analyze(&function, session.known_callees(), &|_| None);
        let known = analysis
            .entry_state(less)
            .map(State::known)
            .unwrap_or_default();
        assert!(
            known
                .iter()
                .any(|predicate| predicate.comparison == Comparison::Less
                    && predicate.left.as_symbol().is_some()
                    && predicate.right.as_symbol().is_some()),
            "the `Less` edge must know `left < right`, got {known:?}"
        );
    }

    /// The default of a multiway switch excludes every named case.
    #[test]
    fn a_multiway_switch_default_negates_every_named_case() {
        with_analysis(
            "fn classify(i: int, n: int) -> int {\
                match cmp(i, n) { Less => 0, Equal => 1, _ => 2 }\
            }",
            "classify",
            |function, analysis, _| {
                let default_state = function
                    .blocks()
                    .filter_map(|block| analysis.entry_state(block))
                    .find(|state| {
                        state
                            .known()
                            .iter()
                            .any(|predicate| predicate.comparison == Comparison::LessOrEqual)
                            && state
                                .known()
                                .iter()
                                .any(|predicate| predicate.comparison == Comparison::NotEqual)
                    });
                assert!(
                    default_state.is_some(),
                    "the default arm must exclude both `Less` and `Equal`"
                );
            },
        );
    }

    /// Writing a slot must not silently update the facts stated about what it held, and must not
    /// carry the old contents forward either.
    #[test]
    fn rewriting_a_slot_gives_it_a_new_symbol() {
        with_analysis(
            "fn twice(a: int) -> int { let mut x = a; x = x + 1; x = x + 1; x }",
            "twice",
            |function, analysis, _| {
                let mut seen = FxHashSet::default();
                for block in function.blocks() {
                    let Some(state) = analysis.entry_state(block) else {
                        continue;
                    };
                    seen.extend(state.current.values().copied());
                }
                assert!(
                    analysis.symbols().len() > seen.len(),
                    "superseded definitions must remain named, or the relation between them is lost"
                );
            },
        );
    }

    /// The loop this whole item exists for: the index arrives from an un-inlined
    /// `Iterator::next`, whose iterator is a `&mut` argument. Folding has to escape that place;
    /// this analysis must not, or the induction variable is out of reach.
    #[test]
    fn a_known_callees_mutable_argument_stays_tracked() {
        with_analysis(
            "fn total(mut a: [int]) -> int { let mut t = 0; for i in 0..len(a) { t = t + i }; t }",
            "total",
            |function, analysis, _| {
                let (folding_escapes, _) = escaping_roots(function, &|_| false);
                let ours = folding_escapes
                    .iter()
                    .filter(|root| analysis.is_escaped(root))
                    .count();
                assert!(
                    ours < folding_escapes.len(),
                    "modelling the known callees' writes must keep at least one root tracked that \
                     folding has to give up on"
                );
            },
        );
    }

    /// A loop is where a definition-site naming scheme either settles or spins: the back edge
    /// rejoins a block with a state that disagrees with the one it was first entered with. Every
    /// reachable block having a state is the observable form of "the fixpoint terminated".
    #[test]
    fn a_loop_reaches_a_fixpoint() {
        with_analysis(
            "fn total(mut a: [int]) -> int { let mut t = 0; for i in 0..len(a) { t = t + i }; t }",
            "total",
            |function, analysis, _| {
                assert!(
                    function.blocks().count() > 3,
                    "the fixture must actually contain a loop"
                );
                assert!(
                    function
                        .blocks()
                        .all(|block| analysis.entry_state(block).is_some()),
                    "every block of a loop must be reached"
                );
            },
        );
    }

    /// Every predicate any block is entered under.
    fn assumptions(function: &Function, analysis: &Analysis) -> Vec<Predicate> {
        function
            .blocks()
            .filter_map(|block| analysis.entry_state(block))
            .flat_map(|state| state.known().to_vec())
            .collect()
    }

    /// A guard is the only place the analysis learns anything it did not compute: the arm is
    /// reached exactly when the condition held, so both arms must carry opposite facts.
    #[test]
    fn both_arms_of_a_guard_are_entered_under_opposite_facts() {
        with_analysis(
            "fn smaller(a: int, b: int) -> int { if a < b { a } else { b } }",
            "smaller",
            |function, analysis, _| {
                let assumed = assumptions(function, analysis);
                let taken: Vec<_> = assumed
                    .iter()
                    .filter(|predicate| predicate.comparison == Comparison::Less)
                    .collect();
                assert!(
                    !taken.is_empty(),
                    "the taken arm must be entered knowing `a - b < 0`, got {assumed:?}"
                );
                assert!(
                    taken
                        .iter()
                        .any(|predicate| assumed.contains(&predicate.negated())),
                    "the other arm must be entered knowing the negation, got {assumed:?}"
                );
            },
        );
    }

    /// The negation of an order swaps its sides, and negating twice gives back the original, or an
    /// arm reached twice would drift.
    #[test]
    fn negating_an_order_swaps_its_sides() {
        let left = Affine {
            constant: 3,
            ..Affine::symbol(SymbolId::new(0))
        };
        let right = Affine::symbol(SymbolId::new(1));
        let less = Predicate::between(&left, Comparison::Less, &right).unwrap();
        let negated = less.negated();
        assert_eq!(
            negated,
            Predicate::between(&right, Comparison::LessOrEqual, &left).unwrap()
        );
        assert_eq!(negated.negated(), less);
        let equal = Predicate::between(&left, Comparison::Equal, &right).unwrap();
        assert_eq!(
            equal,
            Predicate::between(&right, Comparison::Equal, &left).unwrap(),
            "an equality is one fact whichever side is written first"
        );
        assert_eq!(equal.negated().negated(), equal);
    }

    /// A goal decided by its own constants needs nothing assumed, and one that is not must not be
    /// waved through by an unrelated fact.
    #[test]
    fn entailment_refuses_what_it_cannot_show() {
        let mut state = State::default();
        let zero = Affine::constant(0);
        let below = |constant| {
            Predicate::between(&Affine::constant(constant), Comparison::Less, &zero).unwrap()
        };
        assert!(state.implies(&below(-1)), "`-1 < 0` holds on its own");
        assert!(!state.implies(&below(0)), "`0 < 0` does not");

        let symbol = |index| Affine::symbol(SymbolId::new(index));
        let goal = Predicate::between(&symbol(0), Comparison::Less, &zero).unwrap();
        assert!(!state.implies(&goal), "nothing is known about the symbol");
        state.assume(Predicate::between(&symbol(1), Comparison::Less, &zero).unwrap());
        assert!(
            !state.implies(&goal),
            "a fact about another symbol must not decide this one"
        );
        state.assume(goal.clone());
        assert!(state.implies(&goal));
    }

    #[test]
    fn unsigned_bounds_edges_preserve_the_conjunction_and_failure_disjunction() {
        let offset = Affine::symbol(SymbolId::new(0));
        let length = Affine::symbol(SymbolId::new(1));
        let lower =
            Predicate::between(&Affine::constant(0), Comparison::LessOrEqual, &offset).unwrap();
        let upper = Predicate::between(&offset, Comparison::Less, &length).unwrap();
        let mut state = State::default();
        let edge = |state: &State, success| bounds_edge_predicates(state, offset, length, success);
        assert_eq!(edge(&state, true), vec![lower.clone(), upper.clone()]);
        assert!(
            edge(&state, false).is_empty(),
            "failure alone establishes neither alternative"
        );
        state.assume(lower.clone());
        assert_eq!(edge(&state, false), vec![upper.negated()]);
        state = State::default();
        state.assume(upper.clone());
        assert_eq!(edge(&state, false), vec![lower.negated()]);
        state.assume(lower.clone());
        assert!(
            edge(&state, false)
                .iter()
                .any(|predicate| state.implies(&predicate.negated())),
            "a fully proved range makes the failure edge infeasible"
        );
    }

    /// `int` wraps, so an order is not decided by the difference of its sides: `x + 1 < x` holds at
    /// the maximum, and `0 <= MIN` never does although `0 - MIN` wraps to `MIN`.
    #[test]
    fn an_order_is_not_decided_by_a_wrapping_difference() {
        let state = State::default();
        let x = Affine::symbol(SymbolId::new(0));
        let successor = x.add(&Affine::constant(1)).unwrap();
        let wrapped = Predicate::between(&successor, Comparison::Less, &x).unwrap();
        assert!(!state.implies(&wrapped));
        assert!(!state.implies(&wrapped.negated()));
        let minimum = Predicate::between(
            &Affine::constant(0),
            Comparison::LessOrEqual,
            &Affine::constant(Int::MIN),
        )
        .unwrap();
        assert!(!state.implies(&minimum));
        assert!(state.implies(&minimum.negated()));

        let known =
            Predicate::between(&x, Comparison::Less, &Affine::symbol(SymbolId::new(1))).unwrap();
        let shifted = Predicate::between(
            &successor,
            Comparison::Less,
            &Affine::symbol(SymbolId::new(1))
                .add(&Affine::constant(1))
                .unwrap(),
        )
        .unwrap();
        assert!(
            !known.entails(&shifted),
            "`x < y` must not give `x + 1 < y + 1`, which fails at `y` the maximum"
        );
    }

    /// `len + i < len` needs both `i < 0` and `0 <= len`: without the second, the sum can wrap.
    #[test]
    fn a_negative_offset_stays_below_a_non_negative_base() {
        let zero = Affine::constant(0);
        let len = Affine::symbol(SymbolId::new(0));
        let i = Affine::symbol(SymbolId::new(1));
        let goal = Predicate::between(&len.add(&i).unwrap(), Comparison::Less, &len).unwrap();
        let mut state = State::default();
        state.assume(Predicate::between(&i, Comparison::Less, &zero).unwrap());
        assert!(!state.implies(&goal), "`len` may be negative");
        state.assume(Predicate::between(&zero, Comparison::LessOrEqual, &len).unwrap());
        assert!(state.implies(&goal));
    }

    const LOOP: &str =
        "fn total(mut a: [int]) -> int { let mut t = 0; for i in 0..len(a) { t = t + a[i] }; t }";

    /// An index nothing bounds, so its check survives every pass.
    const UNPROVABLE: &str = "fn get(mut a: [int], i: int) -> int { a[i] }";

    /// The shape `dot` is written in: an accumulator seeded from the first element, then a loop over
    /// the rest. The seed's successful check proves `0 < len`, hence the `1 <= len` ordering the
    /// range needs to count upwards.
    const LOOP_FROM_ONE: &str = "fn total(mut a: [int]) -> int { let mut t = a[0]; for i in 1..len(a) { t = t + a[i] }; t }";

    /// Whether any block is entered knowing `0 <= x` and `x < end` for one value `x`: the bounds a
    /// range loop's body needs for its check to be removable, whether its step is a call or inlined.
    fn bounds_its_cursor(function: &Function, analysis: &Analysis) -> bool {
        function.blocks().any(|block| {
            analysis.entry_state(block).is_some_and(|state| {
                state.known().iter().any(|lower| {
                    lower.comparison == Comparison::LessOrEqual
                        && lower.left.as_constant() == Some(0)
                        && lower.right.as_symbol().is_some_and(|value| {
                            state.known().iter().any(|upper| {
                                upper.comparison == Comparison::Less
                                    && upper.left.as_symbol() == Some(value)
                            })
                        })
                })
            })
        })
    }

    /// The accesses in `function` that still check their index, including inlined checks.
    fn checked_accesses(function: &Function, known: &KnownCallees) -> usize {
        let checked = |operation: &Operation| {
            operation.diverges()
                || matches!(
                    resolved_callee(operation, known, &|_| None),
                    Some(KnownCallee::ArrayResolveIndex | KnownCallee::ArrayIndex)
                )
        };
        function
            .blocks()
            .map(|block| {
                let block = function.block(block);
                let invoked = match &block.terminator().kind {
                    TerminatorKind::Invoke { operation, .. } => Some(operation),
                    _ => None,
                };
                block
                    .operations()
                    .iter()
                    .chain(invoked)
                    .filter(|operation| checked(operation))
                    .count()
            })
            .sum()
    }

    /// The body of a zero-based range loop is entered knowing its cursor bounded from both sides.
    /// With the access's check gone, only the induction can have said so.
    #[test]
    fn a_zero_based_range_loop_bounds_its_cursor() {
        with_analysis(LOOP, "total", |function, analysis, known| {
            assert_eq!(checked_accesses(function, known), 0);
            assert!(
                bounds_its_cursor(function, analysis),
                "the loop body must be entered knowing `0 <= i < len`"
            );
        });
    }

    /// The analysis is two walks to a fixpoint, so a consumer has to be able to skip it. The
    /// fixture that *keeps* a check is one whose index nothing bounds.
    #[test]
    fn a_body_with_no_bounds_check_is_filtered_out() {
        with_analysis(UNPROVABLE, "get", |function, analysis, known| {
            assert!(worth_analyzing(function, known, &|_| None));
            assert!(
                facts(function, analysis)
                    .iter()
                    .any(|fact| matches!(fact, Fact::InBounds { .. })),
                "the retained unsigned guard must remain visible to relational analysis"
            );
            assert!(
                bounds_its_cursor(function, analysis),
                "the unsigned guard's success edge must establish both signed bounds"
            );
        });
        with_analysis(
            "fn step(i: int) -> int { i + 1 }",
            "step",
            |function, _, known| {
                assert!(!worth_analyzing(function, known, &|_| None));
            },
        );
    }

    /// A check reaching its normal edge is a guard the source did not write, and the length is the
    /// half of it that outlives the access: `a[0]` returning is the only thing in `dot` that says
    /// the array is not empty.
    #[test]
    fn a_check_that_returned_bounds_the_length_it_consulted() {
        with_analysis(
            "fn first(mut a: [int]) -> int { a[0] }",
            "first",
            |function, analysis, _| {
                let bounded = function.blocks().any(|block| {
                    analysis.entry_state(block).is_some_and(|state| {
                        state.known().iter().any(|predicate| {
                            predicate.comparison == Comparison::Less
                                && predicate.left.as_constant() == Some(0)
                                && predicate.right.as_symbol().is_some()
                        })
                    })
                });
                assert!(
                    bounded,
                    "returning from `a[0]` must leave `0 < len` known below it"
                );
            },
        );
    }

    /// The start need only be a non-negative constant. The seed's successful check proves
    /// `0 < len`, which entails the `1 <= len` ascending obligation, so only the seed stays checked.
    #[test]
    fn a_loop_from_one_is_bounded_by_the_check_that_preceded_it() {
        let mut seed_checks = 0;
        with_analysis(
            "fn first(mut a: [int]) -> int { a[0] }",
            "first",
            |function, _, known| seed_checks = checked_accesses(function, known),
        );
        with_analysis(LOOP_FROM_ONE, "total", |function, analysis, known| {
            assert_eq!(checked_accesses(function, known), seed_checks);
            assert!(
                bounds_its_cursor(function, analysis),
                "`1..len(a)` after `a[0]` must bound its cursor from both sides"
            );
        });
        // The same loop without the seed: nothing says `n` is above the start, so the range may
        // count down and the access keeps its check.
        with_analysis(
            "fn total(mut a: [int], n: int) -> int { let mut t = 0; for i in 1..n { t = t + a[i] }; t }",
            "total",
            |function, _, known| {
                assert!(
                    checked_accesses(function, known) > 0,
                    "a range from one to an unknown end must not be assumed ascending"
                );
            },
        );
    }

    /// On integers `x < y` and `x + 1 <= y` are one fact, and the check that returned states the
    /// first where a range from one asks for the second.
    #[test]
    fn a_strict_bound_entails_the_step_above_it() {
        let len = Affine::symbol(SymbolId::new(0));
        let zero = Affine::constant(0);
        let strict = Predicate::between(&zero, Comparison::Less, &len).unwrap();
        let stepped =
            Predicate::between(&Affine::constant(1), Comparison::LessOrEqual, &len).unwrap();
        assert!(strict.entails(&stepped), "`0 < len` must give `1 <= len`");
        assert!(
            !stepped.entails(&strict),
            "the weaker bound must not give back the strict one"
        );
        assert!(
            !strict.entails(
                &Predicate::between(&Affine::constant(2), Comparison::LessOrEqual, &len).unwrap()
            ),
            "only the one step is sound; two would be the strengthening this refuses"
        );
    }

    /// Bounding the width of a form is what keeps every operation on one linear.
    #[test]
    fn an_over_wide_form_is_refused_rather_than_truncated() {
        let wide = Affine {
            constant: 0,
            terms: Terms::from_sorted((0..MAX_TERMS as u32).map(|index| (SymbolId::new(index), 1)))
                .unwrap(),
        };
        assert_eq!(
            wide.add(&Affine::symbol(SymbolId::from_index(MAX_TERMS))),
            None,
            "a sum past the bound must be refused, never silently dropped"
        );
        assert!(
            wide.add(&Affine::symbol(SymbolId::new(0))).is_some(),
            "a sum that merges into an existing term stays within the bound"
        );
    }

    /// A wrapping product can be zero, and a zero term must go, or two equal forms would differ.
    #[test]
    fn a_vanishing_product_drops_its_term() {
        let symbol = Affine::symbol(SymbolId::new(0));
        assert_eq!(
            symbol.scale(1isize << (isize::BITS - 2)).scale(4),
            Affine::constant(0)
        );
    }
}
