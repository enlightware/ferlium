// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Boolean conditions read back through the storage and negations that produced them.
//!
//! Ferlium has no negation operation: `not` is a std call, which
//! [`fold`](super::fold) rewrites into the comparison MIR does have — `comp_eq value false`. What
//! that leaves is a boolean travelling through a local cell before it is tested:
//!
//! ```text
//! %flag = alloca bool
//! %negated = comp_eq %condition false
//! store %negated to %flag
//! %read = load %flag
//! condbr %read, then, else
//! ```
//!
//! Every step of that chain is information the producer already had. This pass walks a boolean
//! back to the register that computes it, counting the negations on the way, and rewrites the
//! consumer to read that register directly — a `condbr` swaps its targets when the count is odd,
//! and a further `comp_eq` against a boolean flips the literal it compares against. Nothing is
//! removed here: the chain becomes unused, and ordinary DCE collects the cell, the store and the
//! load.
//!
//! Both consumers are the same walk, and it stops at the first thing it cannot see through, so a
//! partial resolution still pays.
//!
//! # What the walk is allowed to assume
//!
//! **A register is immutable**, so stepping from a comparison to its scrutinee needs no proof about
//! what happens in between: the operand's definition dominates the comparison's, which dominates
//! every use the walk started from.
//!
//! **A cell is not**, so stepping through one is where the proof lives. The cell must be a local
//! `alloca` whose *only* write is one `store` of a register, whose every other use is a direct
//! read — a `load`, or a `comp_eq` scrutinee — and whose write dominates the read being resolved.
//! Anything else about the cell, including appearing as a call argument or in a terminator,
//! disqualifies it entirely: those are the uses through which its contents could change, or its
//! address escape. The store's operand being a register rather than a literal is part of the same
//! restriction — a literal flag is [`branch_forward`](super::branch_forward)'s shape, proved there
//! against the arms that store it.
//!
//! **Every value the walk reaches is a boolean**, which is what makes flipping a comparison's
//! literal sound rather than a type question. It holds by construction: a walk starts at a
//! `condbr` condition or at a `comp_eq` scrutinee compared against a boolean pattern, and each step
//! either reads such a comparison's scrutinee or a cell that one of those reads.
//!
//! The walk terminates because each step moves to a strictly earlier definition: a register's
//! operand is defined before it, and a cell's store is proved to dominate the read.

use std::cell::OnceCell;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    containers::b,
    hir::value::LiteralValue,
    mir::{
        self, BlockId, Function, Operation, OperationKind,
        dominance::Dominance,
        edit::FunctionEdit,
        terminator::{Terminator, TerminatorKind},
        value::ValueId,
    },
    module::id::Id,
};

use super::site::{OperationIndex, OperationSite};

/// A boolean value, and whether reaching it passed through an odd number of negations.
#[derive(Clone, Copy)]
struct Source {
    value: ValueId,
    negated: bool,
}

/// A `condbr` whose condition is read from somewhere else.
struct BranchRewrite {
    block: BlockId,
    source: Source,
}

/// A `comp_eq` against a boolean whose scrutinee is read from somewhere else.
struct CompareRewrite {
    site: OperationSite,
    source: Source,
    /// The literal the comparison tests against, already flipped for the negations walked through.
    pattern: bool,
}

/// Forwards boolean conditions to the registers that compute them, returning a rewritten function
/// if anything moved.
pub(crate) fn forward_boolean_negations(func: &Function) -> Option<Function> {
    if !may_forward(func) {
        return None;
    }
    let resolver = Resolver::new(func);
    let mut branches = Vec::new();
    let mut compares = Vec::new();

    for block in func.blocks() {
        let basic_block = func.block(block);
        for (index, operation) in basic_block.operations().iter().enumerate() {
            let OperationKind::CompareEqual = operation.kind else {
                continue;
            };
            let [scrutinee, pattern] = operation.operands.as_ref() else {
                continue;
            };
            let Some(pattern) = bool_operand(func, pattern) else {
                continue;
            };
            let site = OperationSite {
                block,
                index: OperationIndex::from_index(index),
            };
            let Some(source) = resolver.resolve_scrutinee(scrutinee, site) else {
                continue;
            };
            compares.push(CompareRewrite {
                site,
                source,
                pattern: pattern != source.negated,
            });
        }

        if let TerminatorKind::CondBr { condition, .. } = &basic_block.terminator().kind
            && let mir::Value::Register(condition) = condition
            && let Some(source) = resolver.resolve(*condition)
        {
            branches.push(BranchRewrite { block, source });
        }
    }

    if branches.is_empty() && compares.is_empty() {
        return None;
    }

    let mut edit = FunctionEdit::new(func.clone());
    for compare in compares {
        let operation =
            &mut edit.block_mut(compare.site.block).operations[compare.site.index.as_index()];
        operation.operands[0] = mir::Value::Register(compare.source.value);
        operation.operands[1] = mir::Value::Pattern(b(LiteralValue::new_native(compare.pattern)));
    }
    for branch in branches {
        let terminator = &mut edit.block_mut(branch.block).terminator;
        let TerminatorKind::CondBr {
            then_target,
            else_target,
            ..
        } = terminator.kind
        else {
            unreachable!("planned against this block's condbr terminator");
        };
        let (then_target, else_target) = if branch.source.negated {
            (else_target, then_target)
        } else {
            (then_target, else_target)
        };
        *terminator = Terminator::cond_br(
            terminator.span,
            mir::Value::Register(branch.source.value),
            then_target,
            else_target,
        );
    }
    Some(edit.finish_unverified())
}

/// Whether any boolean in this body is even written as a comparison.
///
/// Every negation is one, and so is every consumer this pass rewrites, so a body without one has
/// nothing to forward — while a body with a branch, which is most of them, would otherwise pay for
/// a definition map, a use census and a dominator tree to discover that. A boolean copied from cell
/// to cell with no comparison anywhere is deliberately out of scope: forwarding it saves a load,
/// and `copy_forward` already proves that kind of storage redundant.
fn may_forward(func: &Function) -> bool {
    func.blocks().any(|block| {
        func.block(block)
            .operations()
            .iter()
            .any(|operation| matches!(operation.kind, OperationKind::CompareEqual))
    })
}

/// The body's definitions and forwardable cells, and the dominance the cell proof needs.
struct Resolver<'a> {
    func: &'a Function,
    definitions: FxHashMap<ValueId, OperationSite>,
    /// The local storage of the body, which is what a walk may have to look through.
    allocas: FxHashSet<ValueId>,
    /// Built on the first walk that reaches an `alloca`, and not before: a census and a dominator
    /// tree are the expensive half of this pass, and a condition computed by a comparison the
    /// branch can test directly — the common case — never asks for either.
    cells: OnceCell<Cells>,
}

/// What a cell holds, and the dominance that says where that answer is valid.
struct Cells {
    stored: FxHashMap<ValueId, (ValueId, OperationSite)>,
    dominance: Dominance,
}

impl<'a> Resolver<'a> {
    fn new(func: &'a Function) -> Self {
        let mut definitions = FxHashMap::default();
        let mut allocas = FxHashSet::default();
        for block in func.blocks() {
            for (index, operation) in func.block(block).operations().iter().enumerate() {
                let Some(result) = operation.result_id() else {
                    continue;
                };
                definitions.insert(
                    result,
                    OperationSite {
                        block,
                        index: OperationIndex::from_index(index),
                    },
                );
                if matches!(operation.kind, OperationKind::Alloca { .. }) {
                    allocas.insert(result);
                }
            }
        }
        Self {
            func,
            definitions,
            allocas,
            cells: OnceCell::new(),
        }
    }

    fn cells(&self) -> &Cells {
        self.cells.get_or_init(|| {
            let successors: Vec<Vec<usize>> = self
                .func
                .blocks()
                .map(|block| {
                    self.func
                        .block(block)
                        .terminator()
                        .successors()
                        .map(|target| target.as_index())
                        .collect()
                })
                .collect();
            Cells {
                stored: forwardable_cells(self.func, &self.allocas),
                dominance: Dominance::of(&successors, self.func.entry().as_index()),
            }
        })
    }

    /// What a `condbr` condition ultimately reads, when that is not the condition itself.
    fn resolve(&self, value: ValueId) -> Option<Source> {
        let start = Source {
            value,
            negated: false,
        };
        self.walk(start).filter(|source| source.value != value)
    }

    /// What a comparison's scrutinee ultimately reads, when that is not the scrutinee itself.
    ///
    /// A comparison names its scrutinee by operand, so the walk starts one step earlier than a
    /// condition's: the scrutinee may already be a cell, which a `condbr` condition cannot be.
    fn resolve_scrutinee(&self, scrutinee: &mir::Value, at: OperationSite) -> Option<Source> {
        let start = Source {
            value: self.read(scrutinee, at)?,
            negated: false,
        };
        let resolved = match self.walk(start) {
            Some(resolved) => resolved,
            // The scrutinee was a cell whose contents nothing further explains: comparing the
            // stored register directly is still one place read less.
            None if self.is_materialized(start.value) => start,
            None => return None,
        };
        (as_register(scrutinee) != Some(resolved.value)).then_some(resolved)
    }

    /// Walks back as far as the proof reaches, or `None` when it does not reach at all.
    ///
    /// Every value passed through is the same boolean up to the negations counted, so the walk may
    /// stop at any of them and keeps the last that is a *materialized* one. That is what a
    /// condition has to be, and the walk does cross places — a cell it cannot see through ends it
    /// on the place itself, one step past the register that read it.
    fn walk(&self, start: Source) -> Option<Source> {
        let mut current = start;
        let mut resolved = None;
        while let Some(next) = self.step(current) {
            current = next;
            if self.is_materialized(next.value) {
                resolved = Some(next);
            }
        }
        resolved
    }

    /// Whether a register holds a boolean rather than the place of one.
    ///
    /// The two forms the walk sees through are also the only two that materialize a boolean into a
    /// register, so this is the same list read the other way round.
    fn is_materialized(&self, value: ValueId) -> bool {
        self.definitions.get(&value).is_some_and(|site| {
            matches!(
                self.operation(*site).kind,
                OperationKind::Load | OperationKind::CompareEqual
            )
        })
    }

    /// One step back: from a boolean to what computed it.
    fn step(&self, from: Source) -> Option<Source> {
        let site = *self.definitions.get(&from.value)?;
        let operation = self.operation(site);
        match operation.kind {
            // A load reads a cell; the cell proof says what the cell holds.
            OperationKind::Load => Some(Source {
                value: self.read(&operation.operands[0], site)?,
                negated: from.negated,
            }),
            // A comparison against a boolean *is* a negation, or an identity.
            OperationKind::CompareEqual => {
                let pattern = bool_operand(self.func, &operation.operands[1])?;
                Some(Source {
                    value: self.read(&operation.operands[0], site)?,
                    negated: from.negated != !pattern,
                })
            }
            _ => None,
        }
    }

    /// The register an operand read at `at` yields: itself when it already is one, and the register
    /// stored into it when it is a cell this pass may see through.
    fn read(&self, operand: &mir::Value, at: OperationSite) -> Option<ValueId> {
        let value = as_register(operand)?;
        if !self.allocas.contains(&value) {
            // Not local storage: either a materialized boolean, which is what the walk is looking
            // for, or a place it may not see through, which the caller's own step then fails on.
            return Some(value);
        }
        let cells = self.cells();
        let &(stored, store) = cells.stored.get(&value)?;
        cells.dominates(store, at).then_some(stored)
    }

    fn operation(&self, site: OperationSite) -> &Operation {
        &self.func.block(site.block).operations()[site.index.as_index()]
    }
}

/// The local cells a boolean may be traced through, each with the register stored into it.
///
/// One pass over every operand occurrence, classifying by the position it appears in: a whitelist,
/// so an unforeseen operation kind excludes the cell rather than being assumed harmless.
fn forwardable_cells(
    func: &Function,
    allocas: &FxHashSet<ValueId>,
) -> FxHashMap<ValueId, (ValueId, OperationSite)> {
    #[derive(Default)]
    struct Uses {
        /// The register the single store wrote, when the single write was one.
        stored: Option<(ValueId, OperationSite)>,
        writes: usize,
        /// A use through which the cell could change, or its address escape.
        opaque: bool,
    }

    let mut cells: FxHashMap<ValueId, Uses> = FxHashMap::default();
    for block in func.blocks() {
        let basic_block = func.block(block);
        for (index, operation) in basic_block.operations().iter().enumerate() {
            let site = OperationSite {
                block,
                index: OperationIndex::from_index(index),
            };
            for (position, operand) in operation.operands.iter().enumerate() {
                let Some(cell) = as_register(operand).filter(|value| allocas.contains(value))
                else {
                    continue;
                };
                let uses = cells.entry(cell).or_default();
                match (&operation.kind, position) {
                    // The one write a forwardable cell may have, and only of a register.
                    (OperationKind::Store, 1) => {
                        uses.writes += 1;
                        uses.stored =
                            as_register(&operation.operands[0]).map(|stored| (stored, site));
                    }
                    // Direct immutable reads.
                    (OperationKind::Load, 0) | (OperationKind::CompareEqual, 0) => {}
                    _ => uses.opaque = true,
                }
            }
        }
        // A terminator names a place only to yield through it, or to pass it to an invoked call.
        for operand in basic_block.terminator().operands() {
            if let Some(cell) = as_register(operand).filter(|value| allocas.contains(value)) {
                cells.entry(cell).or_default().opaque = true;
            }
        }
    }
    cells
        .into_iter()
        .filter_map(|(cell, uses)| {
            (uses.writes == 1 && !uses.opaque).then(|| Some((cell, uses.stored?)))?
        })
        .collect()
}

impl Cells {
    /// Whether a store reaches the read at `at`, and its stored register is defined by then.
    ///
    /// Within one block, block dominance says nothing: a read *before* the store belongs to an
    /// earlier iteration of a loop around it, and the register it would be forwarded to is defined
    /// after the use.
    fn dominates(&self, store: OperationSite, at: OperationSite) -> bool {
        if store.block == at.block {
            return store.index.as_index() < at.index.as_index();
        }
        self.dominance
            .dominates(store.block.as_index(), at.block.as_index())
    }
}

fn as_register(operand: &mir::Value) -> Option<ValueId> {
    match operand {
        mir::Value::Register(value) => Some(*value),
        _ => None,
    }
}

/// The boolean a comparison's pattern operand tests against, in either form lowering emits.
fn bool_operand(func: &Function, operand: &mir::Value) -> Option<bool> {
    let literal = match operand {
        mir::Value::Constant(id) => &func.constant(*id).representation,
        mir::Value::Pattern(literal) => literal,
        _ => return None,
    };
    literal.as_primitive_ty::<bool>().copied()
}

#[cfg(test)]
mod tests {
    use super::forward_boolean_negations;
    use crate::{
        CompilerSession, Location, MirOptimization,
        containers::b,
        hir::{function::ArgConvention, value::LiteralValue},
        mir::{
            self, Function, Operation, ParameterKind, builder::FunctionBuilder,
            terminator::Terminator,
        },
        std::logic::bool_type,
    };

    fn optimized_function(src: &str, name: &str) -> String {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let module = session.emit_mir("negation", src);
        module
            .split(&format!("fn {name}"))
            .nth(1)
            .unwrap_or_else(|| panic!("module has no `{name}`:\n{module}"))
            .split("\nfn ")
            .next()
            .expect("a function has a body")
            .to_string()
    }

    /// The register a rendered `%rN: <role> = <operation>` line defines.
    fn register_defining(body: &str, operation: &str) -> String {
        let line = body
            .lines()
            .find(|line| line.trim_start().starts_with('%') && line.contains(operation))
            .unwrap_or_else(|| panic!("no operation `{operation}` in:\n{body}"));
        let name = line
            .trim_start()
            .split(' ')
            .next()
            .expect("a definition names its register");
        // A definition renders as `%rN: <role> = ...`, so the register name ends at the colon
        // introducing its role annotation.
        name.trim_end_matches(':').to_string()
    }

    /// The constant a block stores, as the pool renders its value.
    fn stored_constant(body: &str, block: &str) -> String {
        let stored = body
            .split(&format!("{block}:\n"))
            .nth(1)
            .unwrap_or_else(|| panic!("no block `{block}` in:\n{body}"))
            .split("store ")
            .nth(1)
            .unwrap_or_else(|| panic!("block `{block}` stores nothing in:\n{body}"))
            .split(' ')
            .next()
            .expect("a store names what it stores")
            .to_string();
        body.lines()
            .find(|line| line.trim_start().starts_with(&format!("{stored}:")))
            .unwrap_or_else(|| panic!("`{stored}` is not in the constant pool of:\n{body}"))
            .split("= ")
            .nth(1)
            .expect("a pool entry renders its value")
            .to_string()
    }

    /// The block a `condbr` takes when its condition holds.
    fn then_target(body: &str) -> String {
        body.split("condbr ")
            .nth(1)
            .unwrap_or_else(|| panic!("no condbr in:\n{body}"))
            .split(", ")
            .nth(1)
            .expect("a condbr names two targets")
            .to_string()
    }

    /// The shape the whole pass exists for: a negated condition costs one comparison and the
    /// branch it already had, with no cell in between.
    #[test]
    fn a_negated_condition_leaves_no_storage_round_trip() {
        let body = optimized_function(
            "fn pick(a: bool) -> int { if not a { 1 } else { 2 } }",
            "pick",
        );
        assert!(
            !body.contains("alloca") && !body.contains("load"),
            "the flag cell and its round trip must be gone:\n{body}"
        );
        let negation = register_defining(&body, "comp_eq %p0 false");
        assert!(
            body.contains(&format!("condbr {negation},")),
            "the branch must test the comparison directly:\n{body}"
        );
        assert_eq!(stored_constant(&body, &then_target(&body)), "1", "{body}");
    }

    /// When the negated value is itself a comparison, nothing has to compute the negation at all:
    /// the branch tests the original and swaps its arms.
    #[test]
    fn negating_a_comparison_inverts_the_branch_instead() {
        let body = optimized_function(
            "fn pick(x: int, y: int) -> int { if not (x < y) { 1 } else { 2 } }",
            "pick",
        );
        assert!(
            !body.contains("false"),
            "the negation itself must disappear:\n{body}"
        );
        let ordering = register_defining(&body, "comp_eq %r");
        assert!(
            body.contains(&format!("condbr {ordering},")),
            "the branch must test the ordering comparison directly:\n{body}"
        );
        assert_eq!(
            stored_constant(&body, &then_target(&body)),
            "2",
            "`x < y` holding must now take the arm the source spelled second:\n{body}"
        );
    }

    /// A cell written on two paths carries a value neither store alone explains, and forwarding
    /// past it would read whichever one the pass happened to see.
    #[test]
    fn a_cell_written_more_than_once_is_not_forwarded() {
        let session = CompilerSession::new();
        let source = branch_on_a_twice_written_flag(&session);
        assert!(
            forward_boolean_negations(&source).is_none(),
            "a flag with two writers must be left alone:\n{}",
            crate::format::FormatWith::format_with(&source, &session.module_env())
        );
    }

    /// ```text
    /// %flag = alloca bool
    /// condbr %argument, left, right
    /// left:  store true to %flag; br join       right: %not = comp_eq %argument false
    ///                                                  store %not to %flag; br join
    /// join:  %read = load %flag; condbr %read, ...
    /// ```
    fn branch_on_a_twice_written_flag(session: &CompilerSession) -> Function {
        let span = Location::new_synthesized();
        let env = session.module_env();
        let mut builder = FunctionBuilder::new("twice_written".into(), Default::default());
        let argument =
            builder.add_parameter(bool_type(), ParameterKind::Parameter(ArgConvention::Let));
        let entry = builder.add_block();
        let left = builder.add_block();
        let right = builder.add_block();
        let join = builder.add_block();
        let exit = builder.add_block();

        let flag = builder
            .append_operation(entry, Operation::alloca(span, bool_type()))
            .expect("alloca produces a place");
        let condition = builder
            .append_operation(
                entry,
                Operation::load(span, mir::Value::Parameter(argument)),
            )
            .expect("load produces a materialized bool");
        builder.set_terminator(entry, Terminator::cond_br(span, condition, left, right));

        let truth = builder.add_constant(bool_type(), LiteralValue::new_native(true), &env);
        builder.append_operation(
            left,
            Operation::store(span, mir::Value::Constant(truth), flag.clone()),
        );
        builder.set_terminator(left, Terminator::goto(span, join));

        let negated = builder
            .append_operation(
                right,
                Operation::compare_eq(
                    span,
                    mir::Value::Parameter(argument),
                    mir::Value::Pattern(b(LiteralValue::new_native(false))),
                ),
            )
            .expect("comp_eq produces a materialized bool");
        builder.append_operation(right, Operation::store(span, negated, flag.clone()));
        builder.set_terminator(right, Terminator::goto(span, join));

        let read = builder
            .append_operation(join, Operation::load(span, flag))
            .expect("load produces a materialized bool");
        builder.set_terminator(join, Terminator::cond_br(span, read, exit, exit));
        builder.set_terminator(exit, Terminator::ret(span));
        builder.finish(env)
    }

    /// A `condbr` on a condition nothing else explains must stay exactly as it is.
    #[test]
    fn an_unexplained_condition_is_left_alone() {
        let body = optimized_function("fn pick(a: bool) -> int { if a { 1 } else { 2 } }", "pick");
        assert!(body.contains("condbr"), "{body}");
        assert!(!body.contains("comp_eq"), "{body}");
    }
}
