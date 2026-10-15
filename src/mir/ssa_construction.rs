// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Values of scalar variables during MIR construction.
//!
//! A variable is a storage location whose value MIR names directly where it can, following the
//! local half of on-the-fly SSA construction (Braun et al. 2013, "Simple and Efficient Construction
//! of SSA Form"): within a block, a read takes the last value written, and the variable's memory is
//! written only where that value leaves the block. MIR has no block parameters yet, so a value
//! crosses an edge through the variable's memory: the block's end writes it, and a block reading a
//! variable before writing it reads that memory once, a value [`remember`](Variables::remember)ed
//! like any other.
//!
//! The variables do not own the memory: their user writes it where [`end_block`](Variables::end_block)
//! or [`demote`](Variables::demote) hands back a value it does not hold yet, and reads it where
//! [`read`](Variables::read) knows no value.

use std::hash::Hash;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    mir::{self, BlockId},
    module::id::Id,
};

/// The value a variable holds at the current end of a block.
struct Definition {
    value: mir::Value,
    /// Whether the variable's memory does not hold `value` yet.
    unwritten: bool,
}

/// The values the variables hold at the current end of a block.
struct BlockValues<V> {
    definitions: FxHashMap<V, Definition>,
    /// The variables in the order of their first definition, so that writing them back is
    /// deterministic. A demoted variable stays listed without a definition.
    order: Vec<V>,
}

impl<V> Default for BlockValues<V> {
    fn default() -> Self {
        Self {
            definitions: FxHashMap::default(),
            order: Vec::new(),
        }
    }
}

/// The scalar variables of a function under construction, and the values they hold per block.
pub(crate) struct Variables<V> {
    declared: FxHashSet<V>,
    /// The variables [`demote`](Variables::demote)d, in the order they were.
    demoted: Vec<V>,
    blocks: FxHashMap<BlockId, BlockValues<V>>,
}

impl<V> Default for Variables<V> {
    fn default() -> Self {
        Self {
            declared: FxHashSet::default(),
            demoted: Vec::new(),
            blocks: FxHashMap::default(),
        }
    }
}

impl<V: Copy + Eq + Hash> Variables<V> {
    /// Tracks `variable`'s value from now on.
    pub(crate) fn declare(&mut self, variable: V) {
        self.declared.insert(variable);
    }

    /// Whether `variable`'s value is tracked.
    pub(crate) fn is_declared(&self, variable: V) -> bool {
        self.declared.contains(&variable)
    }

    /// The value `variable` holds at the current end of `block`, if known there.
    pub(crate) fn read(&self, variable: V, block: BlockId) -> Option<mir::Value> {
        let definition = self.blocks.get(&block)?.definitions.get(&variable)?;
        Some(definition.value.clone())
    }

    /// Records that `variable` holds `value` from the current end of `block`, which its memory does
    /// not hold yet.
    pub(crate) fn write(&mut self, variable: V, block: BlockId, value: mir::Value) {
        self.define(variable, block, value, true);
    }

    /// Records that `variable` holds `value` from the current end of `block`, which was read from
    /// its memory.
    pub(crate) fn remember(&mut self, variable: V, block: BlockId, value: mir::Value) {
        self.define(variable, block, value, false);
    }

    fn define(&mut self, variable: V, block: BlockId, value: mir::Value, unwritten: bool) {
        debug_assert!(
            self.is_declared(variable),
            "an undeclared variable is defined"
        );
        let values = self.blocks.entry(block).or_default();
        let definition = Definition { value, unwritten };
        if values.definitions.insert(variable, definition).is_none() {
            values.order.push(variable);
        }
    }

    /// Ends `block`: forgets its values, and returns those its successors must find in memory.
    pub(crate) fn end_block(&mut self, block: BlockId) -> Vec<(V, mir::Value)> {
        let Some(mut values) = self.blocks.remove(&block) else {
            return Vec::new();
        };
        values
            .order
            .into_iter()
            .filter_map(|variable| {
                let definition = values.definitions.remove(&variable)?;
                definition.unwritten.then_some((variable, definition.value))
            })
            .collect()
    }

    /// Stops tracking `variable`, whose memory is now accessed directly, and returns the values its
    /// memory must receive at the current end of each block that holds one it does not hold yet.
    pub(crate) fn demote(&mut self, variable: V) -> Vec<(BlockId, mir::Value)> {
        if !self.declared.remove(&variable) {
            return Vec::new();
        }
        self.demoted.push(variable);
        let mut writes: Vec<_> = self
            .blocks
            .iter_mut()
            .filter_map(|(&block, values)| {
                let definition = values.definitions.remove(&variable)?;
                definition.unwritten.then_some((block, definition.value))
            })
            .collect();
        writes.sort_by_key(|(block, _)| block.as_index());
        writes
    }

    /// The variables demoted so far, in the order they were.
    pub(crate) fn demoted(&self) -> Vec<V> {
        self.demoted.clone()
    }
}
