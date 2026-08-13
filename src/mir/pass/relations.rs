// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
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

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    hir::function::ArgConvention,
    mir::{
        self, BlockId, Function, Operation, OperationKind, dominance::Dominance,
        terminator::TerminatorKind, value::ValueId,
    },
    module::{FunctionId, id::Id},
    std::math::Int,
    types::r#type::Type,
};

use super::{
    dataflow::{PlaceKey, Root, call_operands, escaping_roots, field_index, successors},
    known_callee::{KnownCallee, KnownCallees, RangeLayout},
    site::{OperationIndex, OperationSite},
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

/// A value the analysis can state facts about.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub(crate) enum Symbol {
    /// The contents a definition put in a place.
    Stored(PlaceKey, DefSite),
    /// A materialized register value. MIR registers are single-assignment, so a register names one
    /// value and needs no definition site of its own.
    Register(ValueId),
}

/// A symbol's dense identity, so that a fact is a few machine words rather than a cloned path.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub(crate) struct SymbolId(u32);

/// The symbols one analysis run has named.
///
/// Lives beside the flow states rather than inside them: interning is monotone and shared, while a
/// state is cloned at every join.
#[derive(Default, Clone)]
pub(crate) struct Symbols {
    ids: FxHashMap<Symbol, SymbolId>,
    names: Vec<Symbol>,
}

impl Symbols {
    fn intern(&mut self, symbol: Symbol) -> SymbolId {
        if let Some(id) = self.ids.get(&symbol) {
            return *id;
        }
        let id =
            SymbolId(u32::try_from(self.names.len()).expect("a function has fewer than 4G values"));
        self.names.push(symbol.clone());
        self.ids.insert(symbol, id);
        id
    }

    pub(crate) fn name(&self, id: SymbolId) -> &Symbol {
        &self.names[id.0 as usize]
    }

    pub(crate) fn len(&self) -> usize {
        self.names.len()
    }
}

/// `constant + Σ coefficient × symbol`.
///
/// Ferlium's `int` wraps, and so does this: every combination below is computed with wrapping
/// arithmetic, so a form is an exact statement about the machine integers rather than an
/// approximation of mathematical ones. A consumer reasoning about magnitudes must account for that
/// itself.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(crate) struct Affine {
    pub constant: Int,
    /// Sorted by symbol, never holding a zero coefficient, never longer than [`MAX_TERMS`].
    terms: Vec<(SymbolId, Int)>,
}

impl Affine {
    pub(crate) fn constant(value: Int) -> Self {
        Self {
            constant: value,
            terms: Vec::new(),
        }
    }

    pub(crate) fn symbol(symbol: SymbolId) -> Self {
        Self {
            constant: 0,
            terms: vec![(symbol, 1)],
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
        match self.terms.as_slice() {
            [(symbol, 1)] if self.constant == 0 => Some(*symbol),
            _ => None,
        }
    }

    /// `self + other`, or `None` when the sum would exceed [`MAX_TERMS`].
    pub(crate) fn add(&self, other: &Affine) -> Option<Affine> {
        let mut terms = self.terms.clone();
        for (symbol, coefficient) in &other.terms {
            match terms.binary_search_by_key(symbol, |(existing, _)| *existing) {
                Ok(index) => terms[index].1 = terms[index].1.wrapping_add(*coefficient),
                Err(index) => terms.insert(index, (*symbol, *coefficient)),
            }
        }
        terms.retain(|(_, coefficient)| *coefficient != 0);
        (terms.len() <= MAX_TERMS).then(|| Affine {
            constant: self.constant.wrapping_add(other.constant),
            terms,
        })
    }

    pub(crate) fn sub(&self, other: &Affine) -> Option<Affine> {
        self.add(&other.scale(-1))
    }

    pub(crate) fn scale(&self, factor: Int) -> Affine {
        if factor == 0 {
            return Affine::constant(0);
        }
        Affine {
            constant: self.constant.wrapping_mul(factor),
            terms: self
                .terms
                .iter()
                .map(|(symbol, coefficient)| (*symbol, coefficient.wrapping_mul(factor)))
                .collect(),
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

/// A comparison against zero.
///
/// Every relation is normalized to `difference ⋈ 0` so that `i < len` and `i - len < 0` are one
/// fact rather than two spellings a consumer would have to reconcile.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(crate) struct Predicate {
    pub difference: Affine,
    pub comparison: Comparison,
}

impl Predicate {
    /// `left ⋈ right`, normalized. `None` when the difference is not affine.
    pub(crate) fn between(left: &Affine, comparison: Comparison, right: &Affine) -> Option<Self> {
        Some(Self {
            difference: left.sub(right)?,
            comparison,
        })
    }

    /// The predicate that holds exactly when this one does not.
    ///
    /// Expressed by flipping the difference rather than by widening [`Comparison`] with the mirror
    /// of every relation: `¬(d < 0)` is `-d ≤ 0`. Keeping one direction is what lets two spellings
    /// of a fact compare equal, which the fixpoint depends on.
    pub(crate) fn negated(&self) -> Self {
        match self.comparison {
            Comparison::Less => Self {
                difference: self.difference.scale(-1),
                comparison: Comparison::LessOrEqual,
            },
            Comparison::LessOrEqual => Self {
                difference: self.difference.scale(-1),
                comparison: Comparison::Less,
            },
            Comparison::Equal => Self {
                difference: self.difference.clone(),
                comparison: Comparison::NotEqual,
            },
            Comparison::NotEqual => Self {
                difference: self.difference.clone(),
                comparison: Comparison::Equal,
            },
        }
    }

    /// Whether this holds outright, from its own constant.
    fn is_certain(&self) -> Option<bool> {
        let constant = self.difference.as_constant()?;
        Some(match self.comparison {
            Comparison::Less => constant < 0,
            Comparison::LessOrEqual => constant <= 0,
            Comparison::Equal => constant == 0,
            Comparison::NotEqual => constant != 0,
        })
    }

    /// Whether holding `self` means `goal` holds too.
    ///
    /// **Deliberately syntactic beyond the constant case.** The obvious strengthening — `d < 0` and
    /// `goal - d` a non-positive constant, therefore `goal < 0` — is *unsound* on Ferlium's `int`,
    /// which wraps: a difference near the bottom of the range plus a negative offset comes back
    /// round as a positive number. Admitting it needs a proof that neither side overflows, which
    /// nothing here has. Normalized affine forms make the syntactic test stronger than it sounds:
    /// two comparisons written over different slots reduce to the same difference whenever their
    /// values do.
    fn entails(&self, goal: &Predicate) -> bool {
        if self.difference != goal.difference {
            return false;
        }
        match (self.comparison, goal.comparison) {
            (a, b) if a == b => true,
            // `<` is the stronger of each pair.
            (Comparison::Less, Comparison::LessOrEqual | Comparison::NotEqual) => true,
            _ => false,
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

/// What a register denotes.
#[derive(Clone, PartialEq, Eq, Debug)]
enum Binding {
    /// The register is a pointer to this slot.
    Place(PlaceKey),
    /// The register holds a materialized value.
    Value,
}

/// The relational state at one program point.
#[derive(Clone, PartialEq, Eq, Default, Debug)]
pub(crate) struct State {
    /// The definition currently supplying each tracked place. A place absent from here has never
    /// been written in this function, and takes [`DefSite::Entry`].
    current: FxHashMap<PlaceKey, DefSite>,
    /// What is known about a symbol. A symbol absent from here is an unknown quantity, which is
    /// still a quantity: it can be named, and two uses of it are the same value.
    facts: FxHashMap<SymbolId, Fact>,
    registers: FxHashMap<ValueId, Binding>,
    /// Comparisons that hold at this point, sorted and deduplicated so that two states holding the
    /// same set compare equal — which is what the fixpoint tests.
    known: Vec<Predicate>,
}

impl State {
    /// The symbol a place's current contents are.
    pub(crate) fn symbol_of(&self, place: &PlaceKey, symbols: &mut Symbols) -> SymbolId {
        let def = self.current.get(place).copied().unwrap_or(DefSite::Entry);
        symbols.intern(Symbol::Stored(place.clone(), def))
    }

    pub(crate) fn fact(&self, symbol: SymbolId) -> Option<&Fact> {
        self.facts.get(&symbol)
    }

    /// The comparisons known to hold here.
    pub(crate) fn known(&self) -> &[Predicate] {
        &self.known
    }

    /// Whether `goal` follows from what is known here.
    pub(crate) fn implies(&self, goal: &Predicate) -> bool {
        goal.is_certain()
            .unwrap_or_else(|| self.known.iter().any(|fact| fact.entails(goal)))
    }

    /// Records a comparison that holds from here on.
    ///
    /// Bounded: a chain of nested conditions would otherwise carry every guard it passed under into
    /// every block below, and the set is a state the fixpoint compares on every edge. Sorted order
    /// makes which ones survive a property of the facts rather than of the walk.
    fn assume(&mut self, predicate: Predicate) {
        if let Err(index) = self.known.binary_search(&predicate) {
            self.known.insert(index, predicate);
            self.known.truncate(MAX_KNOWN);
        }
    }

    /// The slot an operand names, if it names one.
    pub(crate) fn place_of(&self, operand: &mir::Value) -> Option<PlaceKey> {
        match operand {
            mir::Value::Register(id) => match self.registers.get(id)? {
                Binding::Place(place) => Some(place.clone()),
                Binding::Value => None,
            },
            mir::Value::Parameter(id) => Some(PlaceKey::root(Root::Parameter(*id))),
            _ => None,
        }
    }

    /// The affine form of a place's contents.
    ///
    /// A place with nothing known is still one value, and naming it is what relates its two uses.
    /// Before falling back to that, the ancestors are consulted: a range iterator's yield is
    /// recorded on the `Option` as a whole, so reading the payload — however deep inside the option
    /// it sits — has to find it.
    pub(crate) fn place_affine(&self, place: &PlaceKey, symbols: &mut Symbols) -> Affine {
        let symbol = self.symbol_of(place, symbols);
        if let Some(Fact::Value(affine)) = self.fact(symbol) {
            return affine.clone();
        }
        let mut ancestor = place.clone();
        while !ancestor.path.is_empty() {
            ancestor.path.pop();
            let above = self.symbol_of(&ancestor, symbols);
            if let Some(Fact::Yield { value, .. }) = self.fact(above) {
                return Affine::symbol(*value);
            }
        }
        Affine::symbol(symbol)
    }

    /// Every tracked place inside `place`, with the path below it.
    fn within(&self, place: &PlaceKey) -> Vec<PlaceKey> {
        self.current
            .keys()
            .filter(|tracked| *tracked != place && tracked.is_within(place))
            .cloned()
            .collect()
    }

    /// Rebinds `place` to a definition, and forgets what was known about the slots inside it.
    ///
    /// The superseded symbol keeps its fact: it names a value that existed, and a fact about the
    /// *new* contents may well be stated in terms of it. What stops those accumulating is that the
    /// symbol universe is the finite set of program points.
    fn define(&mut self, place: PlaceKey, def: DefSite, symbols: &mut Symbols, fact: Option<Fact>) {
        self.current.retain(|tracked, _| !tracked.is_within(&place));
        self.current.insert(place.clone(), def);
        let symbol = symbols.intern(Symbol::Stored(place, def));
        match fact {
            Some(fact) => {
                self.facts.insert(symbol, fact);
            }
            None => {
                self.facts.remove(&symbol);
            }
        }
    }

    fn join(&self, other: &State) -> State {
        let mut current = FxHashMap::default();
        for (place, def) in &self.current {
            // A place the two edges disagree about, or that only one of them tracks, takes a join
            // symbol: its contents are one of several values and no fact about any of them holds.
            match other.current.get(place) {
                Some(theirs) if theirs == def => {
                    current.insert(place.clone(), *def);
                }
                _ => {}
            }
        }
        let mut facts = FxHashMap::default();
        for (symbol, fact) in &self.facts {
            if other.facts.get(symbol) == Some(fact) {
                facts.insert(*symbol, fact.clone());
            }
        }
        let mut registers = FxHashMap::default();
        for (id, binding) in &self.registers {
            if other.registers.get(id) == Some(binding) {
                registers.insert(*id, binding.clone());
            }
        }
        let known = self
            .known
            .iter()
            .filter(|predicate| other.known.contains(predicate))
            .cloned()
            .collect();
        State {
            current,
            facts,
            registers,
            known,
        }
    }
}

/// The type of storage each root holds, as the body declares it.
///
/// A [`PlaceKey`] carries no type — it is a root and a path of field positions — so recognizing that
/// a slot is an array's length, or a range iterator, means going back to where the storage was
/// declared.
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
    symbols: Symbols,
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
        mut visit: impl FnMut(&Operation, DefSite, &State, &mut Symbols),
    ) {
        let context = Context {
            func,
            semantics: Semantics { known, original_of },
            escaped: self.escaped.clone(),
            types: RootTypes::new(func),
            inductions: self.inductions.clone(),
        };
        let Some(mut state) = self.entry_states.get(&block).cloned() else {
            return;
        };
        for (index, operation) in func.block(block).operations().iter().enumerate() {
            let def = site(block, index);
            visit(operation, def, &state, &mut self.symbols);
            transfer(operation, def, &context, &mut self.symbols, &mut state);
        }
        if let TerminatorKind::Invoke { operation, .. } = &func.block(block).terminator().kind {
            let def = site(block, func.block(block).operations().len());
            visit(operation, def, &state, &mut self.symbols);
        }
    }

    pub(crate) fn symbols(&self) -> &Symbols {
        &self.symbols
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
}

/// Everything one analysis run reads and never changes.
struct Context<'a> {
    func: &'a Function,
    semantics: Semantics<'a>,
    escaped: FxHashSet<Root>,
    types: RootTypes,
    /// The iterator storage whose cursor is known to start at zero and only ever step forward.
    inductions: FxHashMap<Root, Induction>,
}

/// Resolves a call's callee to the semantics the optimizer knows for it.
///
/// Boxed as one closure because both the escape scan and the transfer function ask the same
/// question, once before the walk and once during it.
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
    let candidate = |operation: &Operation| {
        matches!(
            semantics.of(operation),
            Some(KnownCallee::ArrayResolveIndex)
        )
    };
    func.blocks().any(|block| {
        func.block(block).operations().iter().any(candidate)
            || matches!(
                &func.block(block).terminator().kind,
                TerminatorKind::Invoke { operation, .. } if candidate(operation)
            )
    })
}

/// Runs the analysis to fixpoint over `func`.
///
/// **Two passes, not one.** The first assumes no induction; the second re-runs with the loops the
/// first let [`recognize`] confirm. The order is forced: recognizing a cursor that starts at zero
/// means reading what the construction stored, which is a dataflow fact. Bodies with no range loop
/// pay for one pass, which the pre-filter a consumer applies should have excluded anyway.
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
    let (escaped, register_roots) = escaping_roots(func, &|operation| {
        matches!(operation.kind, OperationKind::Drop { .. }) || semantics.of(operation).is_some()
    });

    let mut context = Context {
        func,
        semantics,
        escaped,
        types: RootTypes::new(func),
        inductions: FxHashMap::default(),
    };
    let first = run(&context);
    context.inductions = recognize(&context, &register_roots, &first);
    let settled = if context.inductions.is_empty() {
        first
    } else {
        run(&context)
    };

    let Context {
        escaped,
        types,
        inductions,
        ..
    } = context;
    Analysis {
        entry_states: settled.entry_states,
        exit_states: settled.exit_states,
        symbols: settled.symbols,
        escaped,
        types,
        inductions,
    }
}

/// One run of the fixpoint.
struct Run {
    entry_states: FxHashMap<BlockId, State>,
    exit_states: FxHashMap<BlockId, State>,
    symbols: Symbols,
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
fn run(context: &Context<'_>) -> Run {
    let func = context.func;
    let block_count = func.blocks().count();
    let mut predecessors: Vec<Vec<BlockId>> = vec![Vec::new(); block_count];
    for block in func.blocks() {
        for successor in successors(&func.block(block).terminator().kind) {
            predecessors[successor.as_index()].push(block);
        }
    }

    let mut symbols = Symbols::default();
    let mut entry_states: FxHashMap<BlockId, State> = FxHashMap::default();
    let mut exit_states: FxHashMap<BlockId, State> = FxHashMap::default();
    entry_states.insert(func.entry(), State::default());

    for round in 0.. {
        if round == MAX_ROUNDS {
            return Run {
                entry_states: FxHashMap::default(),
                exit_states: FxHashMap::default(),
                symbols,
            };
        }
        let mut changed = false;
        for block_id in func.blocks() {
            // The entry block's state is not a join of anything; every other block's is the join of
            // what each predecessor sends down the edge into it.
            let entry = if block_id == func.entry() {
                Some(State::default())
            } else {
                let mut joined: Option<State> = None;
                for predecessor in &predecessors[block_id.as_index()] {
                    let Some(exit) = exit_states.get(predecessor) else {
                        continue;
                    };
                    let terminator = &func.block(*predecessor).terminator().kind;
                    let edge = refine(exit, terminator, block_id, &mut symbols);
                    joined = Some(match joined {
                        Some(existing) => rejoin(&existing, &edge, block_id),
                        None => edge,
                    });
                }
                joined
            };
            let Some(entry) = entry else {
                continue;
            };
            if entry_states.get(&block_id) != Some(&entry) {
                changed = true;
            }
            entry_states.insert(block_id, entry.clone());

            let mut state = entry;
            let block = func.block(block_id);
            for (index, operation) in block.operations().iter().enumerate() {
                transfer(
                    operation,
                    site(block_id, index),
                    context,
                    &mut symbols,
                    &mut state,
                );
            }
            if let TerminatorKind::Invoke { operation, .. } = &block.terminator().kind {
                transfer(
                    operation,
                    site(block_id, block.operations().len()),
                    context,
                    &mut symbols,
                    &mut state,
                );
            }
            if exit_states.get(&block_id) != Some(&state) {
                changed = true;
            }
            exit_states.insert(block_id, state);
        }
        if !changed {
            break;
        }
    }

    Run {
        entry_states,
        exit_states,
        symbols,
    }
}

/// The iterator storage whose cursor provably starts at zero and only ever steps forward.
///
/// This is the *zero-based, unit-step* form and nothing more general. What it has to establish is
/// the loop invariant `0 <= cursor`, which no per-edge fact can give: the cursor is a different
/// value on every iteration, and joining the entry value with the stepped one loses the relation
/// that both are non-negative. Recognizing the shape of the whole loop is what replaces that
/// inference, and it is why the plan calls for this before any interval or scalar-evolution
/// machinery.
///
/// A root qualifies when all of the following hold, each of which is a way the invariant could
/// otherwise be broken:
///
/// - it is `alloca` storage for a range iterator, and does not escape;
/// - every write into it other than a step is in **one** block — the construction;
/// - that block dominates every step, so the construction always precedes them;
/// - that block is not reachable from any step, so it is outside the loop and cannot re-run;
/// - after it, both the cursor and the range's lower bound are the constant zero.
///
/// The single-block restriction is what the desugared `for` produces and is deliberately not
/// generalized: a construction spread over blocks would need each one checked against the rest.
fn recognize(
    context: &Context<'_>,
    register_roots: &FxHashMap<ValueId, Root>,
    run: &Run,
) -> FxHashMap<Root, Induction> {
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
        return FxHashMap::default();
    }

    let successor_lists: Vec<Vec<usize>> = func
        .blocks()
        .map(|block| {
            successors(&func.block(block).terminator().kind)
                .into_iter()
                .map(|target| target.as_index())
                .collect()
        })
        .collect();
    let dominance = Dominance::of(&successor_lists, func.entry().as_index());

    let mut recognized = FxHashMap::default();
    for (root, layout, inclusive) in candidates {
        let Some(construction) =
            construction_block(context, register_roots, root, &dominance, &successor_lists)
        else {
            continue;
        };
        let Some(state) = run.exit_states.get(&construction) else {
            continue;
        };
        // A copy, because reading a place has to be able to name one the run never did.
        let mut symbols = run.symbols.clone();
        let cursor = PlaceKey::root(root).field(layout.next);
        let lower = PlaceKey::root(root).field(layout.range).field(layout.start);
        let zero = |place: &PlaceKey, symbols: &mut Symbols| {
            state.place_affine(place, symbols).as_constant() == Some(0)
        };
        if zero(&cursor, &mut symbols) && zero(&lower, &mut symbols) {
            recognized.insert(root, Induction { layout, inclusive });
        }
    }
    recognized
}

/// The one block that writes an iterator outside its steps, if the shape [`recognize`] requires
/// holds.
fn construction_block(
    context: &Context<'_>,
    register_roots: &FxHashMap<ValueId, Root>,
    root: Root,
    dominance: &Dominance,
    successor_lists: &[Vec<usize>],
) -> Option<BlockId> {
    let func = context.func;
    let mut construction: Option<BlockId> = None;
    let mut steps = Vec::new();
    for block in func.blocks() {
        let mut scan = |operation: &Operation| -> bool {
            let writes = writes_into(operation, root, register_roots);
            if !writes {
                return true;
            }
            if context.semantics.of(operation).is_some_and(|known| {
                matches!(
                    known,
                    KnownCallee::RangeNext | KnownCallee::RangeInclusiveNext
                )
            }) {
                steps.push(block);
                return true;
            }
            match construction {
                Some(existing) if existing != block => false,
                _ => {
                    construction = Some(block);
                    true
                }
            }
        };
        for operation in func.block(block).operations() {
            if !scan(operation) {
                return None;
            }
        }
        if let TerminatorKind::Invoke { operation, .. } = &func.block(block).terminator().kind
            && !scan(operation)
        {
            return None;
        }
    }

    let construction = construction?;
    if steps.is_empty() {
        return None;
    }
    let reaches_construction = reachable_from(successor_lists, &steps);
    steps
        .iter()
        .all(|step| dominance.dominates(construction.as_index(), step.as_index()))
        .then_some(())?;
    (!reaches_construction.contains(&construction.as_index())).then_some(construction)
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
fn writes_into(
    operation: &Operation,
    root: Root,
    register_roots: &FxHashMap<ValueId, Root>,
) -> bool {
    let rooted = |operand: &mir::Value| match operand {
        mir::Value::Register(id) => register_roots.get(id) == Some(&root),
        mir::Value::Parameter(id) => root == Root::Parameter(*id),
        _ => false,
    };
    match &operation.kind {
        OperationKind::Alloca { .. } | OperationKind::AllocaPlace { .. } => false,
        // Reads: the place is borrowed and left as it was.
        OperationKind::Load
        | OperationKind::CompareEqual
        | OperationKind::ExtractTag
        | OperationKind::Subfield { .. }
        | OperationKind::DictEntry { .. } => false,
        OperationKind::Store => rooted(&operation.operands[1]),
        OperationKind::Memcpy | OperationKind::Move => {
            rooted(&operation.operands[1]) || operation.operands.iter().skip(2).any(rooted)
        }
        OperationKind::Clear | OperationKind::Drop { .. } => rooted(&operation.operands[0]),
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
/// A `condbr` is the only place a comparison the analysis already understands turns into something
/// it can assume: the arm is taken exactly when the condition holds, so the taken edge carries the
/// predicate and the other carries its negation. This is the whole reason the comparison idiom is
/// reassembled into a [`Predicate`] earlier — a boolean nobody can read says nothing about either
/// arm.
///
/// A `condbr` whose two arms are the same block refines neither: the block is reached whichever way
/// the condition went.
fn refine(
    state: &State,
    terminator: &TerminatorKind,
    successor: BlockId,
    symbols: &mut Symbols,
) -> State {
    let TerminatorKind::CondBr {
        condition,
        then_target,
        else_target,
    } = terminator
    else {
        return state.clone();
    };
    if then_target == else_target {
        return state.clone();
    }
    let mut refined = state.clone();
    match condition_fact(state, condition, symbols) {
        Some(Fact::Truth(predicate)) => refined.assume(if successor == *then_target {
            predicate
        } else {
            predicate.negated()
        }),
        Some(Fact::Implies(predicates)) if successor == *then_target => {
            for predicate in predicates {
                refined.assume(predicate);
            }
        }
        _ => return state.clone(),
    }
    refined
}

/// What is known about the value a terminator branches on.
fn condition_fact(state: &State, condition: &mir::Value, symbols: &mut Symbols) -> Option<Fact> {
    match condition {
        mir::Value::Register(id) => {
            let symbol = symbols.intern(Symbol::Register(*id));
            state.fact(symbol).cloned()
        }
        _ => {
            let place = state.place_of(condition)?;
            let symbol = state.symbol_of(&place, symbols);
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
fn rejoin(existing: &State, incoming: &State, block: BlockId) -> State {
    let mut joined = existing.join(incoming);
    for place in existing.current.keys().chain(incoming.current.keys()) {
        if !joined.current.contains_key(place) {
            joined.current.insert(place.clone(), DefSite::Join(block));
        }
    }
    joined
}

/// The transfer function for one operation.
///
/// `def` names the value any place this operation writes will hold afterwards.
fn transfer(
    operation: &Operation,
    def: DefSite,
    context: &Context<'_>,
    symbols: &mut Symbols,
    state: &mut State,
) {
    let Context {
        func,
        semantics,
        escaped,
        types,
        inductions,
    } = context;
    let tracked = |place: &PlaceKey| !escaped.contains(&place.root);
    match &operation.kind {
        // `alloca_place` is deliberately absent: the escape scan does not register its result as a
        // root, so nothing could ever mark it escaped, and tracking a place the scan cannot escape
        // would be trusting writes it never saw. Its slots stay unnamed until the scan roots them.
        OperationKind::Alloca { .. } => {
            let Some(result) = operation.result_id() else {
                return;
            };
            let root = Root::Alloca(result);
            if escaped.contains(&root) {
                return;
            }
            let place = PlaceKey::root(root);
            state.current.retain(|tracked, _| tracked.root != root);
            state
                .registers
                .insert(result, Binding::Place(place.clone()));
            state.define(place, def, symbols, None);
        }
        OperationKind::Store => {
            let Some(place) = state.place_of(&operation.operands[1]).filter(&tracked) else {
                return;
            };
            let fact = value_fact(&operation.operands[0], func, symbols, state);
            state.define(place, def, symbols, fact);
        }
        OperationKind::Load => {
            let Some(result) = operation.result_id() else {
                return;
            };
            state.registers.insert(result, Binding::Value);
            let fact = state
                .place_of(&operation.operands[0])
                .filter(&tracked)
                .map(|place| {
                    let symbol = state.symbol_of(&place, symbols);
                    // A load with nothing known still yields the *same* value the slot holds, which
                    // is what lets two loads of an unwritten slot compare equal.
                    state
                        .fact(symbol)
                        .cloned()
                        .unwrap_or_else(|| Fact::Value(state.place_affine(&place, symbols)))
                });
            let symbol = symbols.intern(Symbol::Register(result));
            match fact {
                Some(fact) => {
                    state.facts.insert(symbol, fact);
                }
                None => {
                    state.facts.remove(&symbol);
                }
            }
        }
        OperationKind::Subfield { .. } => {
            let Some(result) = operation.result_id() else {
                return;
            };
            let binding = match (
                state.place_of(&operation.operands[0]),
                field_index(&operation.operands[1], func),
            ) {
                (Some(base), Some(index)) if tracked(&base) => {
                    // An array's length is never negative, and no MIR operation says so. Without it
                    // a `for i in 0..len(a)` loop cannot even be shown to count *upwards*, because
                    // a range whose end is below its start counts down.
                    let field = base.field(index);
                    if base.path.is_empty()
                        && index == semantics.known.layouts().array_len
                        && types
                            .of(base.root)
                            .is_some_and(|ty| semantics.known.is_array(ty))
                    {
                        let length = state.place_affine(&field, symbols);
                        if let Some(predicate) = Predicate::between(
                            &Affine::constant(0),
                            Comparison::LessOrEqual,
                            &length,
                        ) {
                            state.assume(predicate);
                        }
                    }
                    Binding::Place(field)
                }
                _ => Binding::Value,
            };
            state.registers.insert(result, binding);
        }
        OperationKind::Memcpy | OperationKind::Move => {
            let source = state.place_of(&operation.operands[0]).filter(&tracked);
            let fact = source.as_ref().map(|place| {
                let symbol = state.symbol_of(place, symbols);
                state
                    .fact(symbol)
                    .cloned()
                    .unwrap_or(Fact::Value(Affine::symbol(symbol)))
            });
            if let Some(destination) = state.place_of(&operation.operands[1]).filter(&tracked) {
                // The fields travel too, and separately from the whole: a struct's own fact says
                // nothing about its fields, and a range is built field by field and then copied
                // into its iterator in one go. Losing the fields there loses the loop's bounds.
                let fields: Vec<_> = source
                    .as_ref()
                    .map(|place| {
                        state
                            .within(place)
                            .into_iter()
                            .map(|inner| {
                                let path = inner.path[place.path.len()..].to_vec();
                                let symbol = state.symbol_of(&inner, symbols);
                                let fact = state
                                    .fact(symbol)
                                    .cloned()
                                    .unwrap_or(Fact::Value(Affine::symbol(symbol)));
                                (path, fact)
                            })
                            .collect()
                    })
                    .unwrap_or_default();
                state.define(destination.clone(), def, symbols, fact);
                // Shallowest first: defining a place forgets the slots inside it, so a deeper field
                // written before its parent would be wiped by the parent's own definition.
                let mut fields = fields;
                fields.sort_by_key(|(path, _)| path.len());
                for (path, fact) in fields {
                    let mut inner = destination.clone();
                    inner.path.extend(path);
                    state.define(inner, def, symbols, Some(fact));
                }
            }
            // A move leaves its source holding nothing nameable; a memcpy preserves it.
            if matches!(operation.kind, OperationKind::Move)
                && let Some(place) = source
            {
                state.define(place, def, symbols, None);
            }
        }
        OperationKind::Clear | OperationKind::Drop { .. } => {
            if let Some(place) = state.place_of(&operation.operands[0]).filter(&tracked) {
                state.define(place, def, symbols, None);
            }
        }
        OperationKind::ExtractTag => {
            let Some(result) = operation.result_id() else {
                return;
            };
            state.registers.insert(result, Binding::Value);
            // An `Ordering` has no payload, so its tag *is* the comparison it stands for.
            let fact = state
                .place_of(&operation.operands[0])
                .filter(&tracked)
                .map(|place| state.symbol_of(&place, symbols))
                .and_then(|symbol| state.fact(symbol).cloned())
                .filter(|fact| matches!(fact, Fact::Ordering { .. } | Fact::Yield { .. }));
            let symbol = symbols.intern(Symbol::Register(result));
            match fact {
                Some(fact) => {
                    state.facts.insert(symbol, fact);
                }
                None => {
                    state.facts.remove(&symbol);
                }
            }
        }
        OperationKind::CompareEqual => {
            let Some(result) = operation.result_id() else {
                return;
            };
            state.registers.insert(result, Binding::Value);
            let symbol = symbols.intern(Symbol::Register(result));
            let fact = comparison_fact(operation, func, symbols, state, &tracked);
            match fact {
                Some(fact) => {
                    state.facts.insert(symbol, fact);
                }
                None => {
                    state.facts.remove(&symbol);
                }
            }
        }
        OperationKind::Call { ty, .. } => {
            let Some(call) = call_operands(&operation.operands, ty) else {
                return;
            };
            let known = semantics.of(operation);
            // Whatever a callee may write through is no longer the value it was, whether or not the
            // callee's meaning is known: knowing what a call computes says nothing about the slots
            // it wrote on the way.
            // The cursor's symbol has to be taken before the step redefines it: the value the
            // option yields is what the iterator held on the way *in*.
            let cursor = known
                .filter(|known| {
                    matches!(
                        known,
                        KnownCallee::RangeNext | KnownCallee::RangeInclusiveNext
                    )
                })
                .and_then(|_| iterator_place(&call.arguments, state))
                .filter(|place| inductions.contains_key(&place.root))
                .map(|place| {
                    let induction = inductions[&place.root];
                    state.symbol_of(&place.field(induction.layout.next), symbols)
                });
            for (operand, convention) in &call.arguments {
                if matches!(convention, ArgConvention::MutableRef)
                    && let Some(place) = state.place_of(operand).filter(&tracked)
                {
                    // A range step writes the cursor and nothing else, so forgetting the whole
                    // iterator would throw away the very bounds the loop is being read for. This is
                    // the precision a resolved callee buys: an unknown one still loses everything.
                    match stepped_cursor(known, &place, types, semantics) {
                        Some(cursor) => state.define(cursor, def, symbols, None),
                        None => state.define(place, def, symbols, None),
                    }
                }
            }
            let fact = known.and_then(|known| result_fact(known, &call.arguments, symbols, state));
            let fact = fact.or_else(|| {
                yield_fact(known?, &call.arguments, inductions, cursor, symbols, state)
            });
            if let Some(place) = state.place_of(call.result).filter(&tracked) {
                state.define(place, def, symbols, fact);
            }
        }
        OperationKind::Clone { .. } => {
            if let Some(place) = state.place_of(&operation.operands[1]).filter(&tracked) {
                state.define(place, def, symbols, None);
            }
        }
        _ => {
            // Not modelled: the escape scan has escaped every place this operation touches, so
            // there is nothing left to invalidate. A result register holds an unnamed value.
            if let Some(result) = operation.result_id() {
                state.registers.insert(result, Binding::Value);
                let symbol = symbols.intern(Symbol::Register(result));
                state.facts.remove(&symbol);
            }
        }
    }
}

/// What a known call leaves in its result slot.
fn result_fact(
    known: KnownCallee,
    arguments: &[(&mir::Value, ArgConvention)],
    symbols: &mut Symbols,
    state: &State,
) -> Option<Fact> {
    let operand = |index: usize| arguments.get(index).map(|(operand, _)| *operand);
    let affine = |index: usize, symbols: &mut Symbols| -> Option<Affine> {
        argument_affine(operand(index)?, symbols, state)
    };
    match known {
        KnownCallee::IntAdd => {
            let left = affine(0, symbols)?;
            let right = affine(1, symbols)?;
            left.add(&right).map(Fact::Value)
        }
        KnownCallee::IntSub => {
            let left = affine(0, symbols)?;
            let right = affine(1, symbols)?;
            left.sub(&right).map(Fact::Value)
        }
        KnownCallee::IntMul => {
            let left = affine(0, symbols)?;
            let right = affine(1, symbols)?;
            left.mul(&right).map(Fact::Value)
        }
        KnownCallee::IntNeg => Some(Fact::Value(affine(0, symbols)?.scale(-1))),
        KnownCallee::IntCmp => Some(Fact::Ordering {
            left: affine(0, symbols)?,
            right: affine(1, symbols)?,
        }),
        // Each of these computes something this representation cannot yet state: a field read, a
        // guarded selection, a wrap, a step whose direction is itself a comparison. The result is
        // still a nameable value, which is what the fresh symbol gives it.
        KnownCallee::ArrayLen
        | KnownCallee::ArrayResolveIndex
        | KnownCallee::ArrayWrapIndex
        | KnownCallee::RangeNext
        | KnownCallee::RangeInclusiveNext => None,
    }
}

/// The cursor a range step writes, for a call that is one.
///
/// `None` for every other call, including one on an iterator whose induction was not recognized:
/// the layout is what makes the narrower write expressible, and it comes from the iterator's type
/// rather than from the loop's shape.
fn stepped_cursor(
    known: Option<KnownCallee>,
    place: &PlaceKey,
    types: &RootTypes,
    semantics: &Semantics<'_>,
) -> Option<PlaceKey> {
    if !matches!(
        known?,
        KnownCallee::RangeNext | KnownCallee::RangeInclusiveNext
    ) || !place.path.is_empty()
    {
        return None;
    }
    let (_, layout) = semantics.known.range_iterator(types.of(place.root)?)?;
    Some(place.field(layout.next))
}

/// The iterator a range step is walking.
fn iterator_place(arguments: &[(&mir::Value, ArgConvention)], state: &State) -> Option<PlaceKey> {
    let (operand, _) = arguments
        .iter()
        .find(|(_, convention)| matches!(convention, ArgConvention::MutableRef))?;
    state.place_of(operand)
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
    symbols: &mut Symbols,
    state: &State,
) -> Option<Fact> {
    if !matches!(
        known,
        KnownCallee::RangeNext | KnownCallee::RangeInclusiveNext
    ) {
        return None;
    }
    let cursor = cursor?;
    let iterator = iterator_place(arguments, state)?;
    let induction = inductions.get(&iterator.root)?;
    let end = state.place_affine(
        &iterator
            .field(induction.layout.range)
            .field(induction.layout.end),
        symbols,
    );
    // Ascending, which for a zero-based range is the end being non-negative. Without it the
    // iterator counts down and every bound below is the wrong way round.
    let ascending = Predicate::between(&Affine::constant(0), Comparison::LessOrEqual, &end)?;
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
fn argument_affine(operand: &mir::Value, symbols: &mut Symbols, state: &State) -> Option<Affine> {
    let place = state.place_of(operand)?;
    Some(state.place_affine(&place, symbols))
}

/// The fact for an operand used as a materialized value.
fn value_fact(
    operand: &mir::Value,
    func: &Function,
    symbols: &mut Symbols,
    state: &State,
) -> Option<Fact> {
    match operand {
        mir::Value::Constant(id) => func
            .constant(*id)
            .representation
            .as_primitive_ty::<Int>()
            .map(|value| Fact::Value(Affine::constant(*value))),
        mir::Value::Register(id) => {
            let symbol = symbols.intern(Symbol::Register(*id));
            state.fact(symbol).cloned()
        }
        _ => None,
    }
}

/// The truth a `comp_eq` against an `Ordering` tag establishes.
fn comparison_fact(
    operation: &Operation,
    func: &Function,
    symbols: &mut Symbols,
    state: &State,
    tracked: &impl Fn(&PlaceKey) -> bool,
) -> Option<Fact> {
    let scrutinee = match state.place_of(&operation.operands[0]) {
        Some(place) if tracked(&place) => {
            let symbol = state.symbol_of(&place, symbols);
            state.fact(symbol).cloned()
        }
        Some(_) => None,
        None => value_fact(&operation.operands[0], func, symbols, state),
    }?;
    let mir::Value::Pattern(pattern) = &operation.operands[1] else {
        return None;
    };
    let tag = pattern.as_variant_tag()?;
    match scrutinee {
        Fact::Ordering { left, right } => {
            let predicate = match tag.as_str() {
                "Less" => Predicate::between(&left, Comparison::Less, &right)?,
                "Greater" => Predicate::between(&right, Comparison::Less, &left)?,
                "Equal" => Predicate::between(&left, Comparison::Equal, &right)?,
                _ => return None,
            };
            Some(Fact::Truth(predicate))
        }
        // One direction only: the payload is in range when the option is `Some`, and a `None`
        // says nothing about a value that is not there.
        Fact::Yield { present_when, .. } if tag.as_str() == "Some" => {
            Some(Fact::Implies(present_when))
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
        let known = KnownCallees::new(session.raw_modules());
        let artifacts = session
            .mir_artifacts_for(module_id, MirOptimization::Enabled)
            .expect("optimized artifacts were just built");
        let function = artifacts
            .bodies()
            .iter()
            .flatten()
            .find(|body| body.name.as_str() == name)
            .expect("the function was declared");
        let mut analysis = analyze(function, &known, &|_| None);
        check(function, &mut analysis, &known);
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

    /// A comparison must survive the three operations lowering spreads it over — a call producing
    /// an `Ordering`, a tag extraction and an equality test — and arrive as one predicate.
    #[test]
    fn a_comparison_becomes_a_predicate_on_the_difference() {
        with_analysis(
            "fn below(i: int, n: int) -> bool { i < n }",
            "below",
            |function, analysis, _| {
                let predicates: Vec<_> = facts(function, analysis)
                    .into_iter()
                    .filter_map(|fact| match fact {
                        Fact::Truth(predicate) => Some(predicate),
                        _ => None,
                    })
                    .collect();
                assert!(
                    predicates
                        .iter()
                        .any(|predicate| predicate.comparison == Comparison::Less
                            && predicate.difference.terms().len() == 2),
                    "`i < n` must become `i - n < 0`, got {predicates:?}"
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
                let mut symbols = Symbols::default();
                let mut seen = FxHashSet::default();
                for block in function.blocks() {
                    let Some(state) = analysis.entry_state(block) else {
                        continue;
                    };
                    for place in state.current.keys() {
                        seen.insert(state.symbol_of(place, &mut symbols));
                    }
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
    /// this analysis must not, or the induction variable is out of reach before step 3 starts.
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

    /// The negation has to be expressible in the one direction predicates are normalized to, or a
    /// guard would refine only the arm it was written for.
    #[test]
    fn negating_a_predicate_flips_the_difference_rather_than_the_relation() {
        let difference = Affine {
            constant: 3,
            terms: vec![(SymbolId(0), 1)],
        };
        let less = Predicate {
            difference: difference.clone(),
            comparison: Comparison::Less,
        };
        let negated = less.negated();
        assert_eq!(negated.comparison, Comparison::LessOrEqual);
        assert_eq!(negated.difference, difference.scale(-1));
        assert_eq!(
            negated.negated(),
            less,
            "negation must be its own inverse, or an arm reached twice would drift"
        );
    }

    /// A goal decided by its own constant needs nothing assumed, and one that is not must not be
    /// waved through by an unrelated fact.
    #[test]
    fn entailment_refuses_what_it_cannot_show() {
        let mut state = State::default();
        let below = |constant| Predicate {
            difference: Affine::constant(constant),
            comparison: Comparison::Less,
        };
        assert!(state.implies(&below(-1)), "`-1 < 0` holds on its own");
        assert!(!state.implies(&below(0)), "`0 < 0` does not");

        let goal = Predicate {
            difference: Affine::symbol(SymbolId(0)),
            comparison: Comparison::Less,
        };
        assert!(!state.implies(&goal), "nothing is known about the symbol");
        state.assume(Predicate {
            difference: Affine::symbol(SymbolId(1)),
            comparison: Comparison::Less,
        });
        assert!(
            !state.implies(&goal),
            "a fact about another symbol must not decide this one"
        );
        state.assume(goal.clone());
        assert!(state.implies(&goal));
    }

    const LOOP: &str =
        "fn total(mut a: [int]) -> int { let mut t = 0; for i in 0..len(a) { t = t + a[i] }; t }";

    /// The whole point of steps 1 through 3, stated where step 4 will ask it: at the bounds check
    /// itself, both halves of its precondition follow from what is known.
    ///
    /// Asked through `implies` against the check's own arguments rather than by matching predicate
    /// shapes, because that is the question the rewrite asks and the only one worth passing.
    #[test]
    fn a_zero_based_range_loop_proves_its_own_bounds_check() {
        with_analysis(LOOP, "total", |function, analysis, known| {
            let mut checks = 0;
            for block in function.blocks() {
                analysis.replay(
                    function,
                    known,
                    &|_| None,
                    block,
                    |operation, _, state, symbols| {
                        let OperationKind::Call { ty, .. } = &operation.kind else {
                            return;
                        };
                        if !matches!(
                            Semantics {
                                known,
                                original_of: &|_| None
                            }
                            .of(operation),
                            Some(KnownCallee::ArrayResolveIndex)
                        ) {
                            return;
                        }
                        let call =
                            call_operands(&operation.operands, ty).expect("a call has operands");
                        let index = argument_affine(call.arguments[0].0, symbols, state)
                            .expect("the index is a place");
                        let length = argument_affine(call.arguments[1].0, symbols, state)
                            .expect("the length is a place");
                        let zero = Affine::constant(0);
                        assert!(
                            state.implies(
                                &Predicate::between(&zero, Comparison::LessOrEqual, &index)
                                    .unwrap()
                            ),
                            "the index must be known non-negative"
                        );
                        assert!(
                            state.implies(
                                &Predicate::between(&index, Comparison::Less, &length).unwrap()
                            ),
                            "the index must be known below the length"
                        );
                        checks += 1;
                    },
                );
            }
            assert_eq!(
                checks, 1,
                "the loop must still contain exactly one bounds check"
            );
        });
    }

    /// The analysis is two walks to a fixpoint, so a consumer has to be able to skip it.
    #[test]
    fn a_body_with_no_bounds_check_is_filtered_out() {
        with_analysis(LOOP, "total", |function, _, known| {
            assert!(worth_analyzing(function, known, &|_| None));
        });
        with_analysis(
            "fn step(i: int) -> int { i + 1 }",
            "step",
            |function, _, known| {
                assert!(!worth_analyzing(function, known, &|_| None));
            },
        );
    }

    /// Bounding the width of a form is what keeps every operation on one linear.
    #[test]
    fn an_over_wide_form_is_refused_rather_than_truncated() {
        let wide = Affine {
            constant: 0,
            terms: (0..MAX_TERMS as u32)
                .map(|index| (SymbolId(index), 1))
                .collect(),
        };
        assert_eq!(
            wide.add(&Affine::symbol(SymbolId(MAX_TERMS as u32))),
            None,
            "a sum past the bound must be refused, never silently dropped"
        );
        assert!(
            wide.add(&Affine::symbol(SymbolId(0))).is_some(),
            "a sum that merges into an existing term stays within the bound"
        );
    }
}
