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
        self, BlockId, Function, Operation, OperationKind, terminator::TerminatorKind,
        value::ValueId,
    },
    module::{FunctionId, id::Id},
    std::math::Int,
};

use super::{
    dataflow::{PlaceKey, Root, call_operands, escaping_roots, field_index, successors},
    known_callee::{KnownCallee, KnownCallees},
    site::{OperationIndex, OperationSite},
};

/// The most terms an affine form may carry.
///
/// A bound rather than a tuning knob: it is what keeps every operation on a form linear in a
/// constant, so the analysis cannot become quadratic in the size of an expression. Index
/// arithmetic reaching this width is not the arithmetic bounds-check elimination is about.
const MAX_TERMS: usize = 4;

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
#[derive(Clone, PartialEq, Eq, Debug)]
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
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
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
#[derive(Clone, PartialEq, Eq, Debug)]
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
        State {
            current,
            facts,
            registers,
        }
    }
}

/// The result of analysing a function.
pub(crate) struct Analysis {
    entry_states: FxHashMap<BlockId, State>,
    exit_states: FxHashMap<BlockId, State>,
    symbols: Symbols,
    escaped: FxHashSet<Root>,
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
        mut visit: impl FnMut(&Operation, DefSite, &State, &Symbols),
    ) {
        let semantics = Semantics { known, original_of };
        let Some(mut state) = self.entry_states.get(&block).cloned() else {
            return;
        };
        for (index, operation) in func.block(block).operations().iter().enumerate() {
            let def = site(block, index);
            visit(operation, def, &state, &self.symbols);
            transfer(
                operation,
                def,
                func,
                &semantics,
                &self.escaped,
                &mut self.symbols,
                &mut state,
            );
        }
        if let TerminatorKind::Invoke { operation, .. } = &func.block(block).terminator().kind {
            let def = site(block, func.block(block).operations().len());
            visit(operation, def, &state, &self.symbols);
        }
    }

    pub(crate) fn symbols(&self) -> &Symbols {
        &self.symbols
    }

    pub(crate) fn is_escaped(&self, root: &Root) -> bool {
        self.escaped.contains(root)
    }
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

/// Runs the analysis to fixpoint over `func`.
pub(crate) fn analyze(
    func: &Function,
    known: &KnownCallees,
    original_of: &dyn Fn(FunctionId) -> Option<FunctionId>,
) -> Analysis {
    let semantics = Semantics { known, original_of };
    // A known callee writes only through the arguments it declares and captures none of them, so
    // its mutable argument stays tracked and `transfer` accounts for the write.
    let (escaped, _) = escaping_roots(func, &|operation| semantics.of(operation).is_some());

    let mut symbols = Symbols::default();
    let mut entry_states: FxHashMap<BlockId, State> = FxHashMap::default();
    entry_states.insert(func.entry(), State::default());

    let mut changed = true;
    while changed {
        changed = false;
        for block_id in func.blocks() {
            let Some(entry) = entry_states.get(&block_id).cloned() else {
                continue;
            };
            let mut state = entry;
            let block = func.block(block_id);
            for (index, operation) in block.operations().iter().enumerate() {
                transfer(
                    operation,
                    site(block_id, index),
                    func,
                    &semantics,
                    &escaped,
                    &mut symbols,
                    &mut state,
                );
            }
            if let TerminatorKind::Invoke { operation, .. } = &block.terminator().kind {
                transfer(
                    operation,
                    site(block_id, block.operations().len()),
                    func,
                    &semantics,
                    &escaped,
                    &mut symbols,
                    &mut state,
                );
            }
            for successor in successors(&block.terminator().kind) {
                let updated = match entry_states.get(&successor) {
                    Some(existing) => rejoin(existing, &state, successor),
                    None => state.clone(),
                };
                if entry_states.get(&successor) != Some(&updated) {
                    entry_states.insert(successor, updated);
                    changed = true;
                }
            }
        }
    }

    // One last walk to record where each block leaves off. The fixpoint only ever propagates entry
    // states, and every consumer asks about a point inside a block.
    let mut exit_states = FxHashMap::default();
    for block_id in func.blocks() {
        let Some(mut state) = entry_states.get(&block_id).cloned() else {
            continue;
        };
        let block = func.block(block_id);
        for (index, operation) in block.operations().iter().enumerate() {
            let def = site(block_id, index);
            transfer(
                operation,
                def,
                func,
                &semantics,
                &escaped,
                &mut symbols,
                &mut state,
            );
        }
        if let TerminatorKind::Invoke { operation, .. } = &block.terminator().kind {
            let def = site(block_id, block.operations().len());
            transfer(
                operation,
                def,
                func,
                &semantics,
                &escaped,
                &mut symbols,
                &mut state,
            );
        }
        exit_states.insert(block_id, state);
    }

    Analysis {
        entry_states,
        exit_states,
        symbols,
        escaped,
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
    func: &Function,
    semantics: &Semantics<'_>,
    escaped: &FxHashSet<Root>,
    symbols: &mut Symbols,
    state: &mut State,
) {
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
                        .unwrap_or(Fact::Value(Affine::symbol(symbol)))
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
                (Some(base), Some(index)) if tracked(&base) => Binding::Place(base.field(index)),
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
                state.define(destination, def, symbols, fact);
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
                .filter(|fact| matches!(fact, Fact::Ordering { .. }));
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
            for (operand, convention) in &call.arguments {
                if matches!(convention, ArgConvention::MutableRef)
                    && let Some(place) = state.place_of(operand).filter(&tracked)
                {
                    state.define(place, def, symbols, None);
                }
            }
            let fact = known.and_then(|known| result_fact(known, &call.arguments, symbols, state));
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

/// The affine form of a value read through a call argument.
///
/// An argument is always a place: MIR has no immediate operands at a call, so a literal reaches one
/// through a slot it was stored into, and that store is where its form was recorded.
fn argument_affine(operand: &mir::Value, symbols: &mut Symbols, state: &State) -> Option<Affine> {
    let place = state.place_of(operand)?;
    let symbol = state.symbol_of(&place, symbols);
    match state.fact(symbol) {
        Some(Fact::Value(affine)) => Some(affine.clone()),
        // An unknown slot is still one value, and naming it is what relates its two uses.
        _ => Some(Affine::symbol(symbol)),
    }
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
    let Fact::Ordering { left, right } = scrutinee else {
        return None;
    };
    let mir::Value::Pattern(pattern) = &operation.operands[1] else {
        return None;
    };
    let predicate = match pattern.as_variant_tag()?.as_str() {
        "Less" => Predicate::between(&left, Comparison::Less, &right)?,
        "Greater" => Predicate::between(&right, Comparison::Less, &left)?,
        "Equal" => Predicate::between(&left, Comparison::Equal, &right)?,
        _ => return None,
    };
    Some(Fact::Truth(predicate))
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
    fn with_analysis(src: &str, name: &str, check: impl FnOnce(&Function, &Analysis)) {
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
        let analysis = analyze(function, &known, &|_| None);
        check(function, &analysis);
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
            |function, analysis| {
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
            |function, analysis| {
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
            |function, analysis| {
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
            |function, analysis| {
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
            |function, analysis| {
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
