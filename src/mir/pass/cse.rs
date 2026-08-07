// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Common-subexpression elimination over the address computations a body repeats.
//!
//! Inlining is what creates the redundancy: splicing an accessor into every call site copies its
//! `subfield` chain along with it, so `swap#spec:[int]` recomputes `subfield @c1 from %p1` — the
//! buffer field of the same array — once per element access. The operations are pure and cheap
//! individually; there are simply many of them.
//!
//! **Dominator-based value numbering.** Each operation is keyed by its kind, its type metadata and
//! the *canonical* identity of each operand, so comparing two arbitrarily deep expressions is one
//! key comparison rather than a tree walk: operands are already canonicalized when an operation is
//! reached, which is what keeps this linear. The table is scoped to the dominator tree — entered on
//! the way down and undone on the way up — so a match is available exactly when its definition
//! dominates the use. That misses a value available on some paths only; catching those needs
//! available-expressions and lazy code motion, a much larger machine and not what these bodies want.
//!
//! **`subfield` only, and the boundary is sharper than "pure".** A `subfield` *derives* a place
//! from its operand: the result is the base's root and path with one index appended, holding no
//! storage of its own. So it is valid exactly where its base is, and the base is valid at the
//! duplicate — that is what the duplicate reads too. No intervening write can invalidate it either,
//! since MIR registers are single-assignment. There is no kill analysis here at all.
//!
//! Three classes are deliberately out, each for its own reason:
//!
//! - **A memory reader** — `load`, `comp_eq`, `extract_tag` — needs an aliasing argument about the
//!   writes in between, which is what provenance is for.
//! - **An owned materialized value**, `build_subscript` among them, cannot be merged at all: such a
//!   register must have exactly one consuming use, and merging is precisely what gives it two.
//! - **`dict_entry` and `subscript_member`**, despite computing a place from evidence that cannot
//!   change. They **allocate a cell** to materialize the function value into, so the place they
//!   yield lives in the current stack region rather than deriving from an operand's. A
//!   `stack_restore` between the two occurrences pops it, and the merged register then names storage
//!   that is gone — which is not a hypothetical: it is what `bank_account` did when they were
//!   included. Merging them needs a kill on `stack_restore`, and is worth doing only if such a pair
//!   is measured to survive one.

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    mir::{
        self, BlockId, Function, OperationKind,
        dominance::Dominance,
        edit::{FunctionEdit, successors},
        value::ValueId,
    },
    module::{ModuleEnv, id::Id},
    types::r#type::Type,
};

/// The identity of a field-address computation: the type of the place it yields, and its canonical
/// operands — the field index and the base place. Two operations sharing one compute one address.
#[derive(Clone, PartialEq, Eq, Hash)]
struct Expression {
    ty: Type,
    operands: Box<[mir::Value]>,
}

/// The operation an expression was first computed by, and where.
#[derive(Clone, Copy)]
struct Available {
    result: ValueId,
    block: BlockId,
}

/// Replaces repeated address computations by their dominating first occurrence, returning a
/// rewritten function if anything was merged.
pub(crate) fn eliminate_common_subexpressions(
    func: &Function,
    env: ModuleEnv<'_>,
) -> Option<Function> {
    let successors: Vec<Vec<usize>> = func
        .blocks()
        .map(|block| {
            successors(func.block(block).terminator())
                .into_iter()
                .map(|target| target.as_index())
                .collect()
        })
        .collect();
    let dominance = Dominance::of(&successors, func.entry().as_index());

    let mut numbering = Numbering {
        func,
        dominance: &dominance,
        available: FxHashMap::default(),
        merged: FxHashMap::default(),
        removed: FxHashMap::default(),
    };
    numbering.walk(func.entry());
    let Numbering {
        merged, removed, ..
    } = numbering;
    if merged.is_empty() {
        return None;
    }

    let mut edit = FunctionEdit::new(func.clone());
    for (block, indices) in &removed {
        let mut index = 0;
        edit.block_mut(*block).operations.retain(|_| {
            let keep = !indices.contains(&index);
            index += 1;
            keep
        });
    }
    edit.visit_operands_mut(|operand| {
        if let mir::Value::Register(id) = operand
            && let Some(representative) = merged.get(id)
        {
            *id = *representative;
        }
    });
    // A merged operation is usually the last reference to the field index it named.
    edit.prune_constants();
    Some(edit.finish(env))
}

struct Numbering<'a> {
    func: &'a Function,
    dominance: &'a Dominance,
    /// The expressions computed by a dominator of the block being walked.
    available: FxHashMap<Expression, Available>,
    /// The result each merged operation is replaced by. A representative is never itself merged —
    /// an expression is looked up under already-canonical operands — so this needs no chasing.
    merged: FxHashMap<ValueId, ValueId>,
    removed: FxHashMap<BlockId, FxHashSet<usize>>,
}

impl Numbering<'_> {
    /// Numbers `block`, then the subtree it dominates, undoing its own entries on the way back up.
    ///
    /// Iterative rather than recursive, for the same reason the dominator computation is: a body's
    /// block count must not be bounded by the host thread's stack.
    fn walk(&mut self, entry: BlockId) {
        // What each entry displaced, so leaving a subtree restores exactly what entering it found.
        let mut undo: Vec<(Expression, Option<Available>)> = Vec::new();
        let mut stack = vec![(entry, Enter::Down)];
        while let Some((block, direction)) = stack.pop() {
            match direction {
                Enter::Up { undo_depth } => {
                    while undo.len() > undo_depth {
                        let (expression, previous) =
                            undo.pop().expect("the log is longer than the depth");
                        match previous {
                            Some(available) => self.available.insert(expression, available),
                            None => self.available.remove(&expression),
                        };
                    }
                }
                Enter::Down => {
                    let depth = undo.len();
                    self.number_block(block, &mut undo);
                    stack.push((block, Enter::Up { undo_depth: depth }));
                    for &child in self.dominance.children(block.as_index()) {
                        stack.push((BlockId::from_index(child), Enter::Down));
                    }
                }
            }
        }
    }

    fn number_block(&mut self, block: BlockId, undo: &mut Vec<(Expression, Option<Available>)>) {
        for (index, operation) in self.func.block(block).operations().iter().enumerate() {
            let OperationKind::Subfield { ty } = operation.kind else {
                continue;
            };
            let result = operation.result_id().expect("a subfield defines a result");
            let operands = operation
                .operands
                .iter()
                .map(|operand| match operand {
                    mir::Value::Register(id) => match self.merged.get(id) {
                        Some(representative) => mir::Value::Register(*representative),
                        None => operand.clone(),
                    },
                    _ => operand.clone(),
                })
                .collect();
            let expression = Expression { ty, operands };
            match self.available.get(&expression) {
                // Dominance makes the merge *correct*; block order is what the verifier walks in
                // when it resolves an operand's role, so a representative must also precede its new
                // use there. Canonical MIR is ordered so that a dominator comes first, which makes
                // this a guard rather than a restriction.
                Some(&available) if available.block.as_index() <= block.as_index() => {
                    self.merged.insert(result, available.result);
                    self.removed.entry(block).or_default().insert(index);
                }
                _ => {
                    let key = expression.clone();
                    let previous = self
                        .available
                        .insert(expression, Available { result, block });
                    undo.push((key, previous));
                }
            }
        }
    }
}

#[derive(Clone, Copy)]
enum Enter {
    Down,
    Up { undo_depth: usize },
}

#[cfg(test)]
mod tests {
    use crate::{CompilerSession, MirOptimization};

    fn optimized(src: &str) -> String {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        session.emit_mir("cse", src)
    }

    /// The body of `name`, up to the next function.
    fn body_of(src: &str, name: &str) -> String {
        let module = optimized(&format!("struct Pair {{ a: int, b: int }}\n{src}"));
        module
            .split(&format!("fn {name}("))
            .nth(1)
            .unwrap_or_else(|| panic!("module has no `{name}`:\n{module}"))
            .split("\nfn ")
            .next()
            .expect("a split always yields a first piece")
            .to_string()
    }

    fn subfields(body: &str) -> usize {
        body.matches("= subfield").count()
    }

    #[test]
    fn a_repeated_field_address_is_computed_once() {
        let body = body_of("fn twice(p: Pair) -> int { p.a + p.a }", "twice");
        assert_eq!(subfields(&body), 1, "one address, computed once:\n{body}");
    }

    #[test]
    fn addresses_of_different_fields_stay_distinct() {
        let body = body_of("fn both(p: Pair) -> int { p.a + p.b }", "both");
        assert_eq!(subfields(&body), 2, "two fields are two addresses:\n{body}");
    }

    /// The scope must be undone on the way back up the dominator tree: neither arm dominates the
    /// other, so neither may reuse the other's address. Merging them would not merely be
    /// unprofitable — the verifier rejects a use its definition does not dominate.
    #[test]
    fn a_field_address_is_not_shared_between_branch_arms() {
        let body = body_of(
            "fn arms(p: Pair, c: bool) -> int { if c { p.a } else { p.a } }",
            "arms",
        );
        assert_eq!(
            subfields(&body),
            2,
            "each arm computes its own address:\n{body}"
        );
    }

    /// A dominating definition is reused across blocks, which is the case the whole dominator walk
    /// exists for — a redundancy inside one block would not need it.
    #[test]
    fn a_dominating_field_address_is_reused_in_a_later_block() {
        let body = body_of(
            "fn guarded(p: Pair, c: bool) -> int { let x = p.a; if c { x + p.a } else { x } }",
            "guarded",
        );
        assert_eq!(
            subfields(&body),
            1,
            "the entry's address dominates the arm's:\n{body}"
        );
    }
}
