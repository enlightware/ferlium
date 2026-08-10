// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

//! Ownership forwarding for self-prefixed string accumulation.
//!
//! Formatting `out = f"{out}{suffix}"` lowers through an empty builder: render `out` into a
//! temporary string, append that complete snapshot to the builder, append the suffix, then replace
//! `out`. Repeating the assignment copies a growing prefix on every iteration. This pass moves
//! `out` into the builder instead, retains the suffix construction unchanged, and moves the builder
//! back at the original assignment commit point.
//!
//! Unlike the structural MIR passes, this rewrite relies on contracts of concrete std operations:
//! `Value<string>::to_string` returns the same string value, appending it to an empty string is
//! semantically the identity, and both appenders — `string_push_str` and `string_push_static_str`
//! — preserve value semantics and normalization. The corresponding contract is documented beside
//! the implementation in `std::string` and in `doc/mir-optimization.md`.
//!
//! The proof is deliberately local and linear. Every participating place is a local string
//! `alloca`; all builder uses are direct calls to one of the two appenders, followed by the
//! compiler's exact assignment tail; the old accumulator has no use between its first rendering
//! and replacement; and every operation is in one block, excluding a source-fallible `invoke`. The whole-function
//! definition/use census is built once, and each candidate walks only the uses of its fresh builder.

use rustc_hash::{FxHashMap, FxHashSet};
use ustr::ustr;

use crate::{
    mir::{self, BlockId, Function, Operation, OperationKind, edit::FunctionEdit, value::ValueId},
    module::{ConcreteTraitImplKey, FunctionId, ModuleEnv, id::Id},
    std::{
        STD_MODULE_ID,
        core_traits_names::VALUE_TRAIT_NAME,
        string::{
            STRING_FROM_STATIC_FUNCTION_NAME, STRING_PUSH_STATIC_STR_FUNCTION_NAME,
            STRING_PUSH_STR_FUNCTION_NAME, StaticStr, string_type,
        },
        value::{VALUE_DROP_METHOD_INDEX, VALUE_TO_STRING_METHOD_INDEX},
    },
    types::r#type::Type,
};

crate::define_id_type!(
    /// A transient position in one block's operation vector, not a stable MIR identity.
    OperationIndex
);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct OperationSite {
    block: BlockId,
    index: OperationIndex,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum UseSite {
    Operation { site: OperationSite, operand: u32 },
    Terminator { block: BlockId, operand: u32 },
}

#[derive(Clone, Copy)]
struct Definition {
    ty: Type,
}

#[derive(Default)]
struct Census {
    definitions: FxHashMap<ValueId, Definition>,
    uses: FxHashMap<ValueId, Vec<UseSite>>,
    use_positions: FxHashMap<(ValueId, UseSite), usize>,
}

impl Census {
    fn new(func: &Function, from_static: FunctionId) -> (Self, Vec<OperationSite>) {
        let mut census = Self::default();
        let mut candidates = Vec::new();
        for block in func.blocks() {
            let basic_block = func.block(block);
            for (index, operation) in basic_block.operations().iter().enumerate() {
                let site = OperationSite {
                    block,
                    index: OperationIndex::from_index(index),
                };
                if let OperationKind::Alloca { ty } = operation.kind
                    && let Some(result) = operation.result_id()
                {
                    census.definitions.insert(result, Definition { ty });
                }
                if is_direct_call(operation, from_static) {
                    candidates.push(site);
                }
                for (operand, value) in operation.operands.iter().enumerate() {
                    census.note(
                        value,
                        UseSite::Operation {
                            site,
                            operand: operand as u32,
                        },
                    );
                }
            }
            for (operand, value) in basic_block.terminator().operands().iter().enumerate() {
                census.note(
                    value,
                    UseSite::Terminator {
                        block,
                        operand: operand as u32,
                    },
                );
            }
        }
        (census, candidates)
    }

    fn note(&mut self, value: &mir::Value, site: UseSite) {
        let mir::Value::Register(id) = value else {
            return;
        };
        let uses = self.uses.entry(*id).or_default();
        self.use_positions.insert((*id, site), uses.len());
        uses.push(site);
    }

    fn is_local_alloca(&self, id: ValueId, ty: Type) -> bool {
        self.definitions.get(&id).is_some_and(|def| def.ty == ty)
    }

    fn position(&self, id: ValueId, site: UseSite) -> Option<usize> {
        self.use_positions.get(&(id, site)).copied()
    }
}

#[derive(Clone, Copy)]
struct StringFunctions {
    from_static: FunctionId,
    push: FunctionId,
    push_static: FunctionId,
    to_string: FunctionId,
    drop: FunctionId,
}

impl StringFunctions {
    fn resolve(env: ModuleEnv<'_>) -> Option<Self> {
        let module = env.module_by_id(STD_MODULE_ID)?;
        let named = |name| {
            module
                .get_local_function_id(ustr(name))
                .map(|function| FunctionId::new(STD_MODULE_ID, function))
        };
        let value_trait = env.expect_std_trait_id(VALUE_TRAIT_NAME);
        let key = ConcreteTraitImplKey::new(value_trait, vec![string_type()]);
        let implementation = module.get_impl_data(*module.get_concrete_impl_by_key(&key)?)?;
        Some(Self {
            from_static: named(STRING_FROM_STATIC_FUNCTION_NAME)?,
            push: named(STRING_PUSH_STR_FUNCTION_NAME)?,
            push_static: named(STRING_PUSH_STATIC_STR_FUNCTION_NAME)?,
            to_string: FunctionId::new(
                STD_MODULE_ID,
                implementation.methods[usize::from(VALUE_TO_STRING_METHOD_INDEX)],
            ),
            drop: FunctionId::new(
                STD_MODULE_ID,
                implementation.methods[usize::from(VALUE_DROP_METHOD_INDEX)],
            ),
        })
    }
}

struct Forward {
    block: BlockId,
    initialize_builder: OperationIndex,
    self_to_string: OperationIndex,
    self_push: OperationIndex,
    rendered_drop: OperationIndex,
    builder_move: OperationIndex,
    builder_drop: OperationIndex,
    accumulator_drop: OperationIndex,
    commit: OperationIndex,
    accumulator: ValueId,
    builder: ValueId,
}

/// Forwards string accumulator ownership, returning `None` when the function has no candidate.
pub(crate) fn forward_string_accumulation(func: &Function, env: ModuleEnv<'_>) -> Option<Function> {
    let functions = StringFunctions::resolve(env)?;
    // Candidate collection shares the definition/use walk, avoiding a second traversal of every
    // operation on the overwhelmingly common no-match path.
    let (census, candidates) = Census::new(func, functions.from_static);
    let mut forwards = Vec::new();
    for site in candidates {
        if let Some(forward) = plan_forward(func, &census, functions, site) {
            forwards.push(forward);
        }
    }
    if forwards.is_empty() {
        return None;
    }

    let mut replacements = FxHashMap::default();
    let mut removals: FxHashMap<BlockId, FxHashSet<OperationIndex>> = FxHashMap::default();
    for forward in forwards {
        let operations = func.block(forward.block).operations();
        let initialize_span = operations[forward.initialize_builder.as_index()].span;
        replacements.insert(
            OperationSite {
                block: forward.block,
                index: forward.initialize_builder,
            },
            Operation::move_value(
                initialize_span,
                mir::Value::Register(forward.accumulator),
                mir::Value::Register(forward.builder),
            ),
        );
        let commit_span = operations[forward.commit.as_index()].span;
        replacements.insert(
            OperationSite {
                block: forward.block,
                index: forward.commit,
            },
            Operation::move_value(
                commit_span,
                mir::Value::Register(forward.builder),
                mir::Value::Register(forward.accumulator),
            ),
        );
        removals.entry(forward.block).or_default().extend([
            forward.self_to_string,
            forward.self_push,
            forward.rendered_drop,
            forward.builder_move,
            forward.builder_drop,
            forward.accumulator_drop,
        ]);
    }

    let mut edit = FunctionEdit::new(func.clone());
    for block in func.blocks() {
        let mut index = 0;
        edit.block_mut(block).operations.retain_mut(|operation| {
            let operation_index = OperationIndex::from_index(index);
            index += 1;
            if removals
                .get(&block)
                .is_some_and(|indices| indices.contains(&operation_index))
            {
                return false;
            }
            if let Some(replacement) = replacements.remove(&OperationSite {
                block,
                index: operation_index,
            }) {
                *operation = replacement;
            }
            true
        });
    }
    Some(edit.finish(env))
}

fn plan_forward(
    func: &Function,
    census: &Census,
    functions: StringFunctions,
    initialize_builder: OperationSite,
) -> Option<Forward> {
    let operations = func.block(initialize_builder.block).operations();
    let initialization = &operations[initialize_builder.index.as_index()];
    let [
        mir::Value::Function(_),
        mir::Value::Register(static_text),
        mir::Value::Register(builder),
    ] = initialization.operands.as_ref()
    else {
        return None;
    };
    if !census.is_local_alloca(*static_text, crate::std::string::static_str_type())
        || !census.is_local_alloca(*builder, string_type())
        || !is_empty_static_initialization(func, census, *static_text, initialize_builder)
    {
        return None;
    }

    // The self rendering is deliberately adjacent to empty-builder construction. A preceding
    // literal or interpolation means the old value is not the builder's identity prefix.
    let self_to_string = OperationSite {
        block: initialize_builder.block,
        index: OperationIndex::from_index(initialize_builder.index.as_index() + 1),
    };
    let rendering = operations.get(self_to_string.index.as_index())?;
    let [
        mir::Value::Function(_),
        mir::Value::Register(accumulator),
        mir::Value::Register(rendered),
    ] = rendering.operands.as_ref()
    else {
        return None;
    };
    if !is_direct_call(rendering, functions.to_string)
        || !census.is_local_alloca(*accumulator, string_type())
        || !census.is_local_alloca(*rendered, string_type())
    {
        return None;
    }

    let builder_uses = census.uses.get(builder)?;
    if builder_uses.len() < 4
        || builder_uses[0] != operation_use(initialize_builder, 2)
        || !matches!(builder_uses[1], UseSite::Operation { .. })
    {
        return None;
    }
    let UseSite::Operation {
        site: self_push,
        operand: 1,
    } = builder_uses[1]
    else {
        return None;
    };
    if self_push.block != initialize_builder.block
        || self_push.index.as_index() <= self_to_string.index.as_index()
        || !operations[self_to_string.index.as_index() + 1..self_push.index.as_index()]
            .iter()
            .all(|operation| matches!(operation.kind, OperationKind::Alloca { .. }))
        || !is_string_push(
            &operations[self_push.index.as_index()],
            functions.push,
            *builder,
            *rendered,
        )
    {
        return None;
    }

    let rendered_drop = OperationSite {
        block: initialize_builder.block,
        index: OperationIndex::from_index(self_push.index.as_index() + 1),
    };
    if !is_string_drop(
        operations.get(rendered_drop.index.as_index())?,
        functions.drop,
        *rendered,
    ) || census.uses.get(rendered)?.as_slice()
        != [
            operation_use(self_to_string, 2),
            operation_use(self_push, 2),
            operation_use(rendered_drop, 0),
        ]
    {
        return None;
    }

    let [builder_move_use, builder_drop_use] =
        &builder_uses[builder_uses.len().checked_sub(2)?..]
    else {
        return None;
    };
    let UseSite::Operation {
        site: builder_move,
        operand: 0,
    } = *builder_move_use
    else {
        return None;
    };
    let UseSite::Operation {
        site: builder_drop,
        operand: 0,
    } = *builder_drop_use
    else {
        return None;
    };
    if builder_move.block != initialize_builder.block
        || builder_drop.block != initialize_builder.block
        || builder_drop.index.as_index() != builder_move.index.as_index() + 1
    {
        return None;
    }
    for use_site in &builder_uses[2..builder_uses.len() - 2] {
        let UseSite::Operation { site, operand: 1 } = *use_site else {
            return None;
        };
        let operation = &operations[site.index.as_index()];
        // Both appenders qualify: the f-string desugaring emits `string_push_static_str` for its
        // literal segments and `string_push_str` for its interpolations, so a single accumulation
        // normally mixes them. Only the second operand — the suffix — differs, and this check reads
        // the first, the builder.
        if site.block != initialize_builder.block
            || !(is_string_push_target(operation, functions.push, *builder)
                || is_string_push_target(operation, functions.push_static, *builder))
        {
            return None;
        }
    }

    let move_to_temporary = &operations[builder_move.index.as_index()];
    let [
        mir::Value::Register(moved_builder),
        mir::Value::Register(temporary),
    ] = move_to_temporary.operands.as_ref()
    else {
        return None;
    };
    if !matches!(move_to_temporary.kind, OperationKind::Move)
        || moved_builder != builder
        || !census.is_local_alloca(*temporary, string_type())
        || !is_string_drop(
            &operations[builder_drop.index.as_index()],
            functions.drop,
            *builder,
        )
    {
        return None;
    }

    let accumulator_drop = OperationSite {
        block: initialize_builder.block,
        index: OperationIndex::from_index(builder_drop.index.as_index() + 1),
    };
    let commit = OperationSite {
        block: initialize_builder.block,
        index: OperationIndex::from_index(builder_drop.index.as_index() + 2),
    };
    if !is_string_drop(
        operations.get(accumulator_drop.index.as_index())?,
        functions.drop,
        *accumulator,
    ) || !is_move(
        operations.get(commit.index.as_index())?,
        *temporary,
        *accumulator,
    ) || census.uses.get(temporary)?.as_slice()
        != [operation_use(builder_move, 1), operation_use(commit, 0)]
    {
        return None;
    }

    // No later read of the old accumulator may occur before it is replaced. Looking up the first
    // use in the already ordered census makes this constant work per candidate even when one local
    // is accumulated repeatedly in a loop body.
    let self_use = operation_use(self_to_string, 1);
    let position = census.position(*accumulator, self_use)?;
    let accumulator_uses = census.uses.get(accumulator)?;
    if accumulator_uses.get(position + 1) != Some(&operation_use(accumulator_drop, 0))
        || accumulator_uses.get(position + 2) != Some(&operation_use(commit, 1))
    {
        return None;
    }

    Some(Forward {
        block: initialize_builder.block,
        initialize_builder: initialize_builder.index,
        self_to_string: self_to_string.index,
        self_push: self_push.index,
        rendered_drop: rendered_drop.index,
        builder_move: builder_move.index,
        builder_drop: builder_drop.index,
        accumulator_drop: accumulator_drop.index,
        commit: commit.index,
        accumulator: *accumulator,
        builder: *builder,
    })
}

fn operation_use(site: OperationSite, operand: u32) -> UseSite {
    UseSite::Operation { site, operand }
}

fn is_empty_static_initialization(
    func: &Function,
    census: &Census,
    place: ValueId,
    materialization: OperationSite,
) -> bool {
    let Some(uses) = census.uses.get(&place) else {
        return false;
    };
    let [
        UseSite::Operation {
            site: store,
            operand: 1,
        },
        materialization_use,
    ] = uses.as_slice()
    else {
        return false;
    };
    if *materialization_use != operation_use(materialization, 1)
        || store.block != materialization.block
        || store.index.as_index() >= materialization.index.as_index()
    {
        return false;
    }
    let operation = &func.block(store.block).operations()[store.index.as_index()];
    let [mir::Value::Constant(id), mir::Value::Register(destination)] = operation.operands.as_ref()
    else {
        return false;
    };
    matches!(operation.kind, OperationKind::Store)
        && *destination == place
        && func
            .constant(*id)
            .representation
            .as_primitive_ty::<StaticStr>()
            .is_some_and(|value| value.as_str().is_empty())
}

fn is_direct_call(operation: &Operation, callee: FunctionId) -> bool {
    matches!(operation.kind, OperationKind::Call { .. })
        && operation.operands.first() == Some(&mir::Value::Function(callee))
}

fn is_string_push_target(operation: &Operation, callee: FunctionId, target: ValueId) -> bool {
    is_direct_call(operation, callee)
        && matches!(operation.operands.get(1), Some(mir::Value::Register(id)) if *id == target)
}

fn is_string_push(
    operation: &Operation,
    callee: FunctionId,
    target: ValueId,
    suffix: ValueId,
) -> bool {
    is_string_push_target(operation, callee, target)
        && matches!(operation.operands.get(2), Some(mir::Value::Register(id)) if *id == suffix)
}

fn is_string_drop(operation: &Operation, callee: FunctionId, target: ValueId) -> bool {
    matches!(operation.kind, OperationKind::Drop { ty } if ty == string_type())
        && matches!(
            operation.operands.as_ref(),
            [mir::Value::Register(id), mir::Value::Function(function)]
                if *id == target && *function == callee
        )
}

fn is_move(operation: &Operation, source: ValueId, destination: ValueId) -> bool {
    matches!(operation.kind, OperationKind::Move)
        && matches!(
            operation.operands.as_ref(),
            [mir::Value::Register(from), mir::Value::Register(to)]
                if *from == source && *to == destination
        )
}

#[cfg(test)]
mod tests {
    use crate::{CompilerSession, MirOptimization};

    fn optimized(src: &str) -> String {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        session.emit_mir("string_accumulate", src)
    }

    fn body_of<'a>(module: &'a str, name: &str) -> &'a str {
        module
            .split(&format!("fn {name}"))
            .nth(1)
            .unwrap_or_else(|| panic!("module has no `{name}`:\n{module}"))
    }

    fn count(body: &str, needle: &str) -> usize {
        body.matches(needle).count()
    }

    #[test]
    fn forwards_a_self_prefixed_string_assignment() {
        let module = optimized(
            "fn append(mut out: string, suffix: string) -> string { \
             out = f\"{out}{suffix}\"; out }",
        );
        let body = body_of(&module, "append");
        assert_eq!(
            count(body, "Value<std::string>::to_string"),
            1,
            "only the suffix should still be rendered:\n{body}"
        );
        assert_eq!(
            count(body, "call std::string_push_str"),
            1,
            "only the suffix should still be appended:\n{body}"
        );
        assert!(
            !body.contains("call std::string_from_static"),
            "the empty builder should be replaced by an ownership move:\n{body}"
        );
    }

    /// Literal segments append through `string_push_static_str` rather than `string_push_str`, so a
    /// format string that mixes text and interpolations presents the builder with both appenders.
    #[test]
    fn forwards_across_a_literal_segment() {
        let module = optimized(
            "fn append(mut out: string, suffix: string) -> string { \
             out = f\"{out}, {suffix}\"; out }",
        );
        let body = body_of(&module, "append");
        assert_eq!(
            count(body, "Value<std::string>::to_string"),
            1,
            "a literal between the interpolations must not block the forwarding:\n{body}"
        );
        assert_eq!(
            count(body, "call std::string_push_static_str"),
            1,
            "the literal segment must still be appended:\n{body}"
        );
    }

    #[test]
    fn refuses_a_literal_before_the_old_accumulator() {
        let module = optimized(
            "fn append(mut out: string, suffix: string) -> string { \
             out = f\"prefix: {out}{suffix}\"; out }",
        );
        let body = body_of(&module, "append");
        assert_eq!(
            count(body, "Value<std::string>::to_string"),
            2,
            "a non-identity prefix must retain the old accumulator rendering:\n{body}"
        );
    }

    #[test]
    fn refuses_an_additional_use_of_the_old_accumulator() {
        let module = optimized(
            "fn append(mut out: string, suffix: string) -> string { \
             out = f\"{out}{suffix}{out}\"; out }",
        );
        let body = body_of(&module, "append");
        assert_eq!(
            count(body, "Value<std::string>::to_string"),
            3,
            "a repeated old-value use must retain the ordinary assignment:\n{body}"
        );
    }
}
