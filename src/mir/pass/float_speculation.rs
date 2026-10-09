// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Computing a chain of float arithmetic without saturating each step, when that is provably exact.
//!
//! Ferlium floats are finite: every `+`, `-` and `*` saturates an overflow to `±f64::MAX`. Clamping
//! after each operation costs a `min`/`max` pair on targets such as Wasm, and it cannot simply be
//! postponed to the end of a chain: `(M + M) - M` is `0` when each step saturates, but `inf - inf`
//! is NaN otherwise, and `(M + M) * 0.5` differs the same way without any NaN at all.
//!
//! What *can* be done exactly is to compute speculatively and check once. With finite operands,
//! IEEE addition, subtraction and multiplication go wrong only by overflowing to an infinity, and
//! non-finiteness is sticky through them: `inf ± finite` and `inf × nonzero` are infinite, while
//! `inf × 0` and `inf - inf` are NaN, which absorbs everything. So if the root of an expression tree
//! computed without saturation is finite, every intermediate that fed it was finite too, and each
//! saturation would have been the identity. The unsaturated result is then bit-for-bit the
//! saturated one, including the sign of zero, which saturation also preserves.
//!
//! The rewrite of a tree whose root writes `D` is therefore:
//!
//! ```text
//! head:  ...non-tree operations of the original span...
//!        raw_float_{add,sub,mul,neg} of the inputs into fresh raw temporaries
//!        ok = raw_float_is_finite(root)
//!        condbr ok, fast, slow
//! fast:  D = raw_float_to_float(root)          // the identity, since root is finite
//!        goto tail
//! slow:  the original tree                    // re-executes on the same inputs
//!        goto tail
//! tail:  ...the rest of the original block...
//! ```
//!
//! The raw values have their own compiler-internal type, `raw_float`, because they break `float`'s
//! contract: no pass, native function or interpreter ever sees an infinite `float`. Conversely,
//! every `float` is a valid `raw_float` with the same representation, so the raw operations read
//! their `float` inputs directly, as MIR allows for arguments a callee only reads. Every raw
//! operation is total, including the conversion back, which maps a non-finite value to zero rather
//! than relying on its position behind the check; a target may elide that fallback where it sees
//! the check (see the Wasm emitter).
//!
//! **Trees, not DAGs.** An intermediate qualifies only if it is a `float` allocation written by one
//! tree operation and read by exactly one other, so a tree has a single exit and needs a single
//! check. A shared value simply ends its tree and becomes an input of the next one.
//!
//! **Division is excluded.** `finite / inf` is zero, so an overflowed divisor would vanish into a
//! finite result the check accepts. Division is also fallible, and so ends a block anyway.
//!
//! **Moving the tree.** Both paths run at the root, so they read the inputs later than the
//! original did. That is exact unless an operation between the tree's first operation and its root
//! may change or release storage. A write is harmless only to an unaliased `float` cell that no
//! earlier tree operation reads, since those that read it later saw the new value in the original
//! too. Otherwise each tree operation copies its inputs to snapshots where it stood, and both paths
//! read those. The rewrite allocates its cells in the entry block, below every stack region a tree
//! spans, such as an inlined callee's.
//!
//! **Final bodies only.** Physical expansion runs the pass on optimized bodies. Semantic MIR, which
//! callers inline, keeps its saturating trees, so an inlined tree joins its caller's.

use std::mem;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    mir::{
        self, BlockId, DebugLocation, Function, Operation, OperationKind, ValueId,
        edit::FunctionEdit, terminator::Terminator,
    },
    module::{FunctionId, ModuleEnv},
    std::{
        logic::bool_type,
        math::{float_type, raw_float_type},
    },
    types::r#type::Type,
};

use super::known_callee::{KnownCallee, KnownCallees};

/// The fewest overflowing operations (additions, subtractions and multiplications) a tree must
/// contain to be worth a check and a duplicated slow path. A single one gains nothing.
const MIN_OVERFLOWING_OPERATIONS: usize = 2;

/// A saturating float arithmetic call and its operands.
struct Arithmetic {
    /// The raw operation computing the same value without saturation.
    raw: KnownCallee,
    inputs: Vec<mir::Value>,
    output: mir::Value,
}

impl Arithmetic {
    fn overflows(&self) -> bool {
        self.raw != KnownCallee::RawFloatNeg
    }
}

/// Function-wide facts about registers, which the tree conditions are phrased in.
struct Registers {
    /// How many times each register appears as an operand, anywhere in the function.
    uses: FxHashMap<ValueId, usize>,
    /// The type each `alloca` register allocates.
    allocas: FxHashMap<ValueId, Type>,
    /// The registers used other than to access a whole cell: as a stored value, a base for a
    /// projection, a call argument other than float arithmetic's, and so on. Only through such a
    /// use can an alias of an allocation come to exist.
    escaped: FxHashSet<ValueId>,
}

impl Registers {
    fn of(
        edit: &FunctionEdit,
        known: &KnownCallees,
        original_of: &impl Fn(FunctionId) -> Option<FunctionId>,
    ) -> Self {
        let mut uses = FxHashMap::default();
        let mut allocas = FxHashMap::default();
        let mut escaped = FxHashSet::default();
        for block in edit.blocks() {
            let block = edit.block(block);
            for operation in &block.operations {
                if let (OperationKind::Alloca { ty }, Some(id)) =
                    (&operation.kind, operation.result_id())
                {
                    allocas.insert(id, *ty);
                }
                count_uses(&mut uses, &operation.operands);
                let is_arithmetic = arithmetic(operation, known, original_of).is_some();
                for (position, operand) in operation.operands.iter().enumerate() {
                    let whole_cell = match operation.kind {
                        OperationKind::Store => position == 1,
                        OperationKind::Load | OperationKind::Memcpy => true,
                        _ => is_arithmetic,
                    };
                    if let (false, mir::Value::Register(id)) = (whole_cell, operand) {
                        escaped.insert(*id);
                    }
                }
            }
            count_uses(&mut uses, block.terminator.operands());
            for operand in block.terminator.operands() {
                if let mir::Value::Register(id) = operand {
                    escaped.insert(*id);
                }
            }
        }
        Self {
            uses,
            allocas,
            escaped,
        }
    }

    /// Whether `value` is a whole `float` allocation.
    fn is_float_alloca(&self, value: &mir::Value) -> bool {
        matches!(value, mir::Value::Register(id) if self.allocas.get(id) == Some(&float_type()))
    }

    /// Whether `value` is a whole `float` allocation that nothing aliases, so that its register is
    /// the only way to read or write it.
    fn is_unaliased_float_cell(&self, value: &mir::Value) -> bool {
        self.is_float_alloca(value)
            && matches!(value, mir::Value::Register(id) if !self.escaped.contains(id))
    }

    /// Whether `value` can be a tree intermediate: a whole `float` allocation used exactly twice,
    /// by the operation writing it and the one reading it, which therefore nothing aliases.
    fn is_intermediate_candidate(&self, value: &mir::Value) -> bool {
        self.is_float_alloca(value)
            && matches!(value, mir::Value::Register(id) if self.uses.get(id) == Some(&2))
    }
}

fn count_uses(uses: &mut FxHashMap<ValueId, usize>, operands: &[mir::Value]) {
    for operand in operands {
        if let mir::Value::Register(id) = operand {
            *uses.entry(*id).or_default() += 1;
        }
    }
}

/// The saturating float arithmetic `operation` performs, if it is one.
fn arithmetic(
    operation: &Operation,
    known: &KnownCallees,
    original_of: &impl Fn(FunctionId) -> Option<FunctionId>,
) -> Option<Arithmetic> {
    let OperationKind::Call { .. } = operation.kind else {
        return None;
    };
    let mir::Value::Function(callee) = operation.operands.first()? else {
        return None;
    };
    let (raw, arity) = match known.resolve(*callee, original_of)? {
        KnownCallee::FloatAdd => (KnownCallee::RawFloatAdd, 2),
        KnownCallee::FloatSub => (KnownCallee::RawFloatSub, 2),
        KnownCallee::FloatMul => (KnownCallee::RawFloatMul, 2),
        KnownCallee::FloatNeg => (KnownCallee::RawFloatNeg, 1),
        _ => return None,
    };
    // Concrete std callees take no hidden evidence: callee, visible arguments, result.
    if operation.operands.len() != arity + 2 {
        return None;
    }
    Some(Arithmetic {
        raw,
        inputs: operation.operands[1..=arity].to_vec(),
        output: operation.operands[arity + 1].clone(),
    })
}

/// A tree found in one block, in operation order, its root last.
struct Tree {
    members: Vec<usize>,
}

/// Finds the first tree in `operations` that is worth speculating.
fn find_tree(
    operations: &[Operation],
    registers: &Registers,
    known: &KnownCallees,
    original_of: &impl Fn(FunctionId) -> Option<FunctionId>,
) -> Option<Tree> {
    let arithmetic: Vec<_> = operations
        .iter()
        .map(|operation| arithmetic(operation, known, original_of))
        .collect();
    // An intermediate is produced and consumed by arithmetic in this block, in that order. Its use
    // count makes both unique.
    let mut producers = FxHashMap::default();
    let mut children: Vec<Vec<usize>> = vec![Vec::new(); operations.len()];
    let mut consumed = vec![false; operations.len()];
    for (index, operation) in arithmetic.iter().enumerate() {
        let Some(operation) = operation else {
            continue;
        };
        for input in &operation.inputs {
            if let Some(&producer) = producers.get(input) {
                children[index].push(producer);
                consumed[producer] = true;
            }
        }
        if registers.is_intermediate_candidate(&operation.output) {
            producers.insert(operation.output.clone(), index);
        }
    }
    (0..operations.len())
        .filter(|&index| arithmetic[index].is_some() && !consumed[index])
        .find_map(|root| {
            let mut members = vec![root];
            let mut pending = vec![root];
            while let Some(index) = pending.pop() {
                members.extend_from_slice(&children[index]);
                pending.extend_from_slice(&children[index]);
            }
            members.sort_unstable();
            let overflowing = members
                .iter()
                .filter(|&&index| arithmetic[index].as_ref().unwrap().overflows())
                .count();
            (overflowing >= MIN_OVERFLOWING_OPERATIONS).then_some(Tree { members })
        })
}

/// Whether an operation between the tree's first member and its root may change or release storage
/// an input reads, so that the slow path, which reads the inputs at the root, needs snapshots.
///
/// Besides operations that write nothing, only a write to an unaliased cell that no earlier member
/// reads is harmless: those members already read their inputs, and later ones read the new value
/// in the original too.
fn needs_snapshots(
    operations: &[Operation],
    members: &[usize],
    registers: &Registers,
    known: &KnownCallees,
    original_of: &impl Fn(FunctionId) -> Option<FunctionId>,
) -> bool {
    let root = *members.last().unwrap();
    let read_before = |index: usize, place: &mir::Value| {
        members
            .iter()
            .take_while(|&&member| member < index)
            .any(|&member| {
                arithmetic(&operations[member], known, original_of)
                    .unwrap()
                    .inputs
                    .contains(place)
            })
    };
    (members[0]..root)
        .filter(|index| members.binary_search(index).is_err())
        .any(|index| {
            let operation = &operations[index];
            match operation.kind {
                OperationKind::Alloca { .. }
                | OperationKind::Load
                | OperationKind::CompareEqual
                | OperationKind::Subfield { .. }
                | OperationKind::StackSave => false,
                OperationKind::Store | OperationKind::Memcpy => {
                    let written = &operation.operands[1];
                    !registers.is_unaliased_float_cell(written) || read_before(index, written)
                }
                _ => true,
            }
        })
}

/// A fresh cell of type `ty`, allocated with the rewrite's other cells in the entry block.
fn fresh_cell(
    edit: &mut FunctionEdit,
    cells: &mut Vec<Operation>,
    span: DebugLocation,
    ty: Type,
) -> mir::Value {
    let mut alloca = Operation::alloca(span, ty);
    let place = edit.assign_new_result(&mut alloca).unwrap();
    cells.push(alloca);
    place
}

/// Appends `callee(arguments..., result)` to `operations`, into a fresh cell of `result_ty`.
#[allow(clippy::too_many_arguments)]
fn call_into_fresh(
    edit: &mut FunctionEdit,
    cells: &mut Vec<Operation>,
    operations: &mut Vec<Operation>,
    span: DebugLocation,
    known: &KnownCallees,
    callee: KnownCallee,
    arguments: impl IntoIterator<Item = mir::Value>,
    result_ty: Type,
) -> mir::Value {
    let place = fresh_cell(edit, cells, span, result_ty);
    let (function, ty) = known.raw_float(callee);
    operations.push(Operation::call(
        span,
        mir::Value::Function(function),
        arguments.into_iter().chain([place.clone()]),
        ty.clone(),
    ));
    place
}

/// Rewrites `tree` of `block` into its fast and slow paths, returning the block holding the
/// operations after it. The cells it allocates are appended to `cells`.
fn speculate(
    edit: &mut FunctionEdit,
    block: BlockId,
    tree: Tree,
    registers: &Registers,
    cells: &mut Vec<Operation>,
    known: &KnownCallees,
    original_of: &impl Fn(FunctionId) -> Option<FunctionId>,
) -> BlockId {
    let root = *tree.members.last().unwrap();
    let operations = mem::take(&mut edit.block_mut(block).operations);
    let snapshots = needs_snapshots(&operations, &tree.members, registers, known, original_of);
    let mut operations = operations.into_iter();
    let original: Vec<_> = operations.by_ref().take(root + 1).collect();
    let rest: Vec<_> = operations.collect();
    let span = original[root].span;

    // The tree leaves the head, where only its snapshots remain, and both paths run at the root.
    // The fast path reads its `float` inputs as raw floats, which they refine.
    let mut head = Vec::with_capacity(original.len() + 2 * tree.members.len());
    let mut fast = Vec::with_capacity(2 * tree.members.len());
    let mut slow = Vec::with_capacity(tree.members.len());
    let mut raw: FxHashMap<mir::Value, mir::Value> = FxHashMap::default();
    let mut root_raw = None;
    let mut destination = None;
    let mut members = tree.members.iter().peekable();
    for (index, mut operation) in original.into_iter().enumerate() {
        if members.next_if(|&&member| member == index).is_none() {
            head.push(operation);
            continue;
        }
        let arithmetic = arithmetic(&operation, known, original_of).unwrap();
        let mut arguments = Vec::with_capacity(arithmetic.inputs.len());
        for (position, input) in arithmetic.inputs.into_iter().enumerate() {
            // A later tree operation names an intermediate by its saturating place.
            if let Some(intermediate) = raw.get(&input) {
                arguments.push(intermediate.clone());
                continue;
            }
            if snapshots && matches!(input, mir::Value::Register(_) | mir::Value::Parameter(_)) {
                let snapshot = fresh_cell(edit, cells, span, float_type());
                head.push(Operation::memcpy(span, input, snapshot.clone()));
                operation.operands[1 + position] = snapshot.clone();
                arguments.push(snapshot);
            } else {
                arguments.push(input);
            }
        }
        let result = call_into_fresh(
            edit,
            cells,
            &mut fast,
            span,
            known,
            arithmetic.raw,
            arguments,
            raw_float_type(),
        );
        raw.insert(arithmetic.output.clone(), result.clone());
        root_raw = Some(result);
        destination = Some(arithmetic.output);
        slow.push(operation);
    }
    let root_raw = root_raw.unwrap();
    head.extend(fast);
    let finite = call_into_fresh(
        edit,
        cells,
        &mut head,
        span,
        known,
        KnownCallee::RawFloatIsFinite,
        [root_raw.clone()],
        bool_type(),
    );
    let mut load = Operation::load(span, finite);
    let condition = edit.assign_new_result(&mut load).unwrap();
    head.push(load);

    let terminator =
        std::mem::replace(&mut edit.block_mut(block).terminator, Terminator::ret(span));
    let tail = edit.add_block(terminator);
    edit.block_mut(tail).operations = rest;
    let fast_block = edit.add_block(Terminator::goto(span, tail));
    let (function, ty) = known.raw_float(KnownCallee::RawFloatToFloat);
    edit.block_mut(fast_block).operations.push(Operation::call(
        span,
        mir::Value::Function(function),
        [root_raw, destination.unwrap()],
        ty.clone(),
    ));
    // The slow path writes its intermediates to fresh cells: their original ones may lie in a
    // stack region released before the root, and nothing else reads them.
    for index in 0..slow.len() - 1 {
        let output = slow[index].operands.last().unwrap().clone();
        let fresh = fresh_cell(edit, cells, span, float_type());
        for operation in &mut slow[index..] {
            for operand in &mut operation.operands {
                if *operand == output {
                    *operand = fresh.clone();
                }
            }
        }
    }
    let slow_block = edit.add_block(Terminator::goto(span, tail));
    edit.block_mut(slow_block).operations = slow;
    let head_block = edit.block_mut(block);
    head_block.operations = head;
    head_block.terminator = Terminator::cond_br(span, condition, fast_block, slow_block);
    tail
}

/// Speculates every eligible float arithmetic tree of `func`.
///
/// Returns the rewritten and verified body, or `None` when there was no tree to speculate.
pub(crate) fn speculate_float_trees(
    func: &Function,
    known: &KnownCallees,
    original_of: &impl Fn(FunctionId) -> Option<FunctionId>,
    env: ModuleEnv<'_>,
) -> Option<Function> {
    // Most bodies have no float arithmetic at all; do not open an edit for them.
    let has_candidate = func.blocks().any(|block| {
        func.block(block)
            .operations()
            .iter()
            .any(|operation| arithmetic(operation, known, original_of).is_some())
    });
    if !has_candidate {
        return None;
    }
    let mut edit = FunctionEdit::new(func.clone());
    // The original use counts describe the trees of the blocks still to scan: a rewrite leaves the
    // operations after its root untouched, and its own operations use only fresh registers besides
    // the tree's inputs, which are no intermediates there.
    let registers = Registers::of(&edit, known, original_of);
    let mut cells = Vec::new();
    let mut pending: Vec<_> = edit.blocks().collect();
    while let Some(block) = pending.pop() {
        // The tail inherits the block's terminator unchanged. An invoke there cannot be a tree
        // member, since float arithmetic is infallible, so it stays after the tree as before.
        if let Some(tree) = find_tree(
            &edit.block(block).operations,
            &registers,
            known,
            original_of,
        ) {
            pending.push(speculate(
                &mut edit,
                block,
                tree,
                &registers,
                &mut cells,
                known,
                original_of,
            ));
        }
    }
    if cells.is_empty() {
        return None;
    }
    // Allocated first, the cells outlive every stack region a tree spans.
    let entry = edit.entry();
    edit.block_mut(entry).operations.splice(0..0, cells);
    edit.reorder_blocks_in_reverse_postorder();
    Some(edit.finish(env))
}

#[cfg(test)]
mod tests {
    use std::mem;

    use crate::{
        CompilerSession, MirOptimization,
        format::FormatWith,
        mir::{Operation, OperationKind, edit::FunctionEdit, pass::scalar_arguments},
        module::Path,
        std::math::float_type,
    };

    /// Optimized physical MIR, where the pass runs.
    fn optimized(src: &str) -> String {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        session.set_physical_mir_optimization(MirOptimization::Enabled);
        let module = session
            .compile(src, "float", Path::single_str("float"))
            .unwrap()
            .module_id;
        session.emit_physical_mir_module(module).unwrap()
    }

    /// The body of a function in the emitted module, up to the next function.
    fn body_of<'a>(module: &'a str, name: &str) -> &'a str {
        let body = module
            .split(&format!("fn {name}("))
            .nth(1)
            .unwrap_or_else(|| panic!("module has no `{name}`:\n{module}"));
        body.split("\nfn ").next().unwrap()
    }

    /// How many calls `body` makes to `callee`, a raw float function or a saturating `Num`
    /// method, whose printed names carry an implementation suffix.
    fn count(body: &str, callee: &str) -> usize {
        body.matches(&format!("{callee}("))
            .chain(body.matches(&format!("{callee}#")))
            .count()
    }

    /// A tree of four saturating operations becomes one check in front of an unsaturated fast
    /// path, with the original tree kept whole as the slow path.
    #[test]
    fn a_float_tree_is_checked_once_and_kept_as_its_slow_path() {
        let module = optimized("fn f(x: float, y: float) -> float { (x * y + 1.0) * x - y }");
        let body = body_of(&module, "f");
        assert_eq!(count(body, "raw_float_is_finite"), 1, "{body}");
        assert_eq!(count(body, "raw_float_to_float"), 1, "{body}");
        assert_eq!(count(body, "raw_float_mul"), 2, "{body}");
        assert_eq!(count(body, "raw_float_add"), 1, "{body}");
        assert_eq!(count(body, "raw_float_sub"), 1, "{body}");
        // The raw operations read the `float` inputs directly.
        assert!(body.contains("raw_float_mul(%p0, %p1, "), "{body}");
        // Nothing between the tree's operations writes, so no input is snapshotted.
        assert_eq!(body.matches("memcpy").count(), 0, "{body}");
        assert_eq!(count(body, "Num<std::float>::mul"), 2, "{body}");
        assert_eq!(count(body, "Num<std::float>::add"), 1, "{body}");
        assert_eq!(count(body, "Num<std::float>::sub"), 1, "{body}");
    }

    /// Semantic MIR keeps its saturating trees, so an inlined callee's tree joins its caller's and
    /// the whole is checked once, rather than the callee's speculated body being speculated again.
    #[test]
    fn an_inlined_tree_joins_its_callers_tree() {
        let module = optimized(
            "fn g(x: float, y: float) -> float { x * y + x }
             fn f(a: float, b: float) -> float { g(a, b) * b - a }",
        );
        let body = body_of(&module, "f");
        assert_eq!(count(body, "raw_float_is_finite"), 1, "{body}");
        assert_eq!(count(body, "raw_float_mul"), 2, "{body}");
        assert_eq!(count(body, "raw_float_add"), 1, "{body}");
        assert_eq!(count(body, "raw_float_sub"), 1, "{body}");
    }

    /// Inputs may project temporary storage released before the root: the tree reads them through
    /// snapshots taken where it stood, as for a local product in an inlined callee.
    #[test]
    fn inputs_released_before_the_root_are_snapshotted() {
        // Inspect speculation before aggregate splitting removes the tuple and its stack region.
        // This pins the lifetime proof independently of later storage cleanup.
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let module = session
            .compile(
                "fn f(a: float, b: float) -> float {
                    let t = { let p = (a, b); p.0 * p.1 };
                    t * b - a
                }",
                "float",
                Path::single_str("float"),
            )
            .unwrap()
            .module_id;
        session.emit_mir_module(module);
        let entry = session
            .expect_fresh_module(module)
            .get_local_function_id("f".into())
            .unwrap();
        let source = session
            .mir_artifacts_for(module, MirOptimization::Enabled)
            .unwrap()
            .get(entry)
            .unwrap();
        let env = session
            .modules()
            .env_for(session.expect_fresh_module(module));
        // Speculation runs in physical lowering, after scalar value arguments are passed as places
        // again.
        let source =
            scalar_arguments::spill_value_arguments(source).unwrap_or_else(|| source.clone());
        // Give the tuple an explicit scoped lifetime, as inlining does. Keep arithmetic result
        // cells outside that region so the original body remains valid after its restoration.
        let mut edit = FunctionEdit::new(source.clone());
        let entry = edit.entry();
        let original = mem::take(&mut edit.block_mut(entry).operations);
        let span = original[0].span;
        let (mut cells, original): (Vec<_>, Vec<_>) = original
            .into_iter()
            .partition(|op| matches!(op.kind, OperationKind::Alloca { ty } if ty == float_type()));
        let mut save = Operation::stack_save(span);
        let marker = edit.assign_new_result(&mut save).unwrap();
        cells.push(save);
        let mut restored = false;
        for operation in original {
            let first_arithmetic = !restored
                && super::arithmetic(&operation, session.known_callees(), &|_| None).is_some();
            cells.push(operation);
            if first_arithmetic {
                cells.push(Operation::stack_restore(span, marker.clone()));
                restored = true;
            }
        }
        assert!(
            restored,
            "fixture must contain arithmetic inside its region"
        );
        edit.block_mut(entry).operations = cells;
        let source = edit.finish(env);
        let speculated =
            super::speculate_float_trees(&source, session.known_callees(), &|_| None, env).unwrap();
        let rendered = speculated.format_with(&env).to_string();
        let body = rendered.as_str();
        assert_eq!(count(body, "raw_float_is_finite"), 1, "{body}");
        let restore = body.find("stack_restore").expect(body);
        let snapshots = body[..restore].matches("memcpy").count();
        assert_eq!(snapshots, 4, "{body}");
    }

    /// A write between the tree's operations to an input an earlier one read changes what the
    /// root would read: the tree reads the input through a snapshot taken before the write.
    #[test]
    fn inputs_written_before_the_root_are_snapshotted() {
        let module = optimized(
            "fn f(x: float, y: float) -> float { let mut a = x; let t = a * y; a = 2.0; (t + a) * y }",
        );
        let body = body_of(&module, "f");
        assert_eq!(count(body, "raw_float_is_finite"), 1, "{body}");
        let store = body.find("store @").expect(body);
        let written = body[store..].split_whitespace().nth(3).unwrap();
        assert!(
            body[..store].contains(&format!("memcpy {written} to")),
            "{body}"
        );
    }

    /// One overflowing operation gains nothing from a check and a duplicate.
    #[test]
    fn a_single_float_operation_is_left_alone() {
        let module = optimized("fn f(x: float, y: float) -> float { -(x * y) }");
        let body = body_of(&module, "f");
        assert_eq!(count(body, "raw_float_is_finite"), 0, "{body}");
    }

    /// A value read twice ends its tree; its readers form a tree of their own that takes it as an
    /// input, so each tree still has a single exit to check.
    #[test]
    fn a_shared_value_ends_its_tree() {
        let module =
            optimized("fn f(x: float, y: float, z: float) -> float { let t = x * y; t + t * z }");
        let body = body_of(&module, "f");
        assert_eq!(count(body, "raw_float_is_finite"), 1, "{body}");
        assert_eq!(count(body, "raw_float_mul"), 1, "{body}");
        assert_eq!(count(body, "raw_float_add"), 1, "{body}");
        // `x * y` itself stays a single saturating operation outside any tree.
        assert_eq!(count(body, "Num<std::float>::mul"), 2, "{body}");
    }

    /// Division is not part of a tree: an overflowed divisor would turn into a finite zero.
    #[test]
    fn division_ends_a_tree() {
        let module = optimized("fn f(x: float, y: float) -> float { 1.0 / (x * y + y) }");
        let body = body_of(&module, "f");
        assert_eq!(count(body, "raw_float_is_finite"), 1, "{body}");
        assert!(!body.contains("raw_float_div"), "{body}");
    }
}
