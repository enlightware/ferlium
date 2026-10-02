// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Local rewrites of adjacent instructions while a function body is emitted.

use std::ops::Range;

use smallvec::SmallVec;
use wasm_encoder::{Function as WasmFunction, Instruction as I, MemArg};

use crate::mir::DebugLocation;

/// Where emitted instructions go: straight into a function, or through [`Code`]'s rewrites.
pub(in crate::wasm) trait Instructions {
    fn instruction(&mut self, instruction: &I<'_>);
}

impl Instructions for WasmFunction {
    fn instruction(&mut self, instruction: &I<'_>) {
        WasmFunction::instruction(self, instruction);
    }
}

impl Instructions for Code {
    #[inline(always)]
    fn instruction(&mut self, instruction: &I<'_>) {
        Code::instruction(self, instruction);
    }
}

/// A set of source spans, those whose work an instruction does: several when a rewrite merged
/// instructions emitted for different ones. It indexes the sets of a [`Code`].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) struct Spans(u32);

impl Spans {
    /// No span: code without source.
    const NONE: Self = Self(0);
}

/// A function body under construction that holds back its last few instructions, so that a
/// negated comparison becomes the complementary one, a comparison with zero a zero test, a set
/// read back a tee, constant additions one or none, a constant address offset part of its load,
/// and a small constant-size copy a load and a store.
///
/// Each instruction carries the spans of the code being emitted when it arrived, and a rewrite
/// gives its result the spans of all the instructions it replaced. The source map is recorded as
/// instructions are written, so it follows the rewrites. Only a branch sees what is held, and
/// nothing is held across it.
pub(super) struct Code {
    function: WasmFunction,
    held: Vec<(I<'static>, Spans)>,
    /// The spans of the code being emitted.
    spans: Spans,
    /// The span sets that [`Spans`] index, the first one empty.
    span_sets: Vec<SmallVec<[DebugLocation; 1]>>,
    /// Written byte ranges with the spans whose work they do, ordered and disjoint.
    source_map: Vec<(Range<usize>, Spans)>,
}

impl Code {
    pub(super) fn new(function: WasmFunction) -> Self {
        Self {
            function,
            held: Vec::new(),
            spans: Spans::NONE,
            span_sets: vec![SmallVec::new()],
            source_map: Vec::new(),
        }
    }

    /// The spans of the code being emitted.
    pub(super) fn spans(&self) -> Spans {
        self.spans
    }

    /// Sets the spans of the code emitted from now on to earlier ones.
    pub(super) fn set_spans(&mut self, spans: Spans) {
        self.spans = spans;
    }

    /// Sets the span of the code emitted from now on, if it has one.
    pub(super) fn set_source(&mut self, source: Option<DebugLocation>) {
        self.spans = match source {
            // Adjacent code of one span then shares its set, and so its range.
            Some(span) if self.span_sets.last().is_some_and(|last| last[..] == [span]) => {
                Spans(self.span_sets.len() as u32 - 1)
            }
            Some(span) => self.span_set(SmallVec::from_elem(span, 1)),
            None => Spans::NONE,
        };
    }

    fn span_set(&mut self, set: SmallVec<[DebugLocation; 1]>) -> Spans {
        let spans = Spans(u32::try_from(self.span_sets.len()).expect("span sets fit in u32"));
        self.span_sets.push(set);
        spans
    }

    /// The function and its source map, with one entry per span of each written range.
    pub(super) fn finish(mut self) -> (WasmFunction, Vec<(Range<usize>, DebugLocation)>) {
        self.flush();
        let span_sets = &self.span_sets;
        let source_map = self
            .source_map
            .iter()
            .flat_map(|(range, spans)| {
                span_sets[spans.0 as usize]
                    .iter()
                    .map(move |span| (range.clone(), *span))
            })
            .collect();
        (self.function, source_map)
    }

    /// Inlined, so that a call site's known instruction selects its path and encoding statically.
    #[inline(always)]
    pub(super) fn instruction(&mut self, instruction: &I<'_>) {
        self.instruction_from(instruction, self.spans);
    }

    #[inline(always)]
    fn instruction_from(&mut self, instruction: &I<'_>, spans: Spans) {
        if let Some(instruction) = holdable(instruction) {
            self.hold(instruction, spans);
        } else if self.held.is_empty() || !self.release(instruction, spans) {
            self.write(instruction, spans);
        }
    }

    #[inline(always)]
    fn write(&mut self, instruction: &I<'_>, spans: Spans) {
        let start = self.function.byte_len();
        self.function.instruction(instruction);
        if spans != Spans::NONE {
            self.record(start, spans);
        }
    }

    fn record(&mut self, start: usize, spans: Spans) {
        let end = self.function.byte_len();
        match self.source_map.last_mut() {
            Some((range, last)) if range.end == start && *last == spans => range.end = end,
            _ => self.source_map.push((start..end, spans)),
        }
    }

    /// Writes every held instruction.
    fn flush(&mut self) {
        let mut held = std::mem::take(&mut self.held);
        for (instruction, spans) in held.drain(..) {
            self.write(&instruction, spans);
        }
        self.held = held;
    }

    /// Removes the last `count` held instructions, returning the union of their spans and `spans`.
    fn merge(&mut self, count: usize, spans: Spans) -> Spans {
        let start = self.held.len() - count;
        let mut merged = Spans::NONE;
        let mut union = None::<SmallVec<[DebugLocation; 1]>>;
        let held = self.held[start..].iter().map(|(_, spans)| *spans);
        for held in held.chain([spans]).collect::<SmallVec<[Spans; 4]>>() {
            if held == merged || held == Spans::NONE {
                continue;
            }
            if merged == Spans::NONE {
                merged = held;
                continue;
            }
            let set = union.get_or_insert_with(|| self.span_sets[merged.0 as usize].clone());
            for span in &self.span_sets[held.0 as usize] {
                if !set.contains(span) {
                    set.push(*span);
                }
            }
        }
        self.held.truncate(start);
        match union {
            Some(set) => self.span_set(set),
            None => merged,
        }
    }

    #[inline(never)]
    fn hold(&mut self, instruction: I<'static>, spans: Spans) {
        self.held.push((instruction, spans));
        loop {
            match self.held.as_slice() {
                // `x == 0` is `x.eqz`.
                [.., (I::I32Const(0), _), (I::I32Eq, _)] => {
                    let spans = self.merge(2, Spans::NONE);
                    self.held.push((I::I32Eqz, spans));
                }
                // A comparison yields 0 or 1, so its negation is the complementary comparison.
                [.., (comparison, _), (I::I32Eqz, _)] => {
                    let Some(complement) = complement(comparison) else {
                        break;
                    };
                    let spans = self.merge(2, Spans::NONE);
                    self.held.push((complement, spans));
                }
                _ => break,
            }
        }
        if self.held.len() > 3 {
            let (first, spans) = self.held.remove(0);
            self.write(&first, spans);
        }
    }

    /// Writes the held instructions before `next`, or absorbs `next` into them, returning whether
    /// it did.
    #[inline(never)]
    fn release(&mut self, next: &I<'_>, spans: Spans) -> bool {
        match (self.held.as_slice(), next) {
            // Adding zero changes nothing; the rest stays held.
            ([.., (I::I32Const(0), _)], I::I32Add) => {
                self.held.pop();
                return true;
            }
            // Constant additions combine, as both wrap.
            (
                [
                    ..,
                    (I::I32Const(first), _),
                    (I::I32Add, _),
                    (I::I32Const(second), _),
                ],
                I::I32Add,
            ) => {
                let sum = first.wrapping_add(*second);
                let spans = self.merge(3, spans);
                if sum != 0 {
                    self.held
                        .extend([(I::I32Const(sum), spans), (I::I32Add, spans)]);
                }
                return true;
            }
            // A constant address offset may move into a load's static offset.
            ([.., (I::I32Const(offset), _), (I::I32Add, _)], _) if *offset > 0 => {
                if let Some(load) = offset_load(next, *offset as u32) {
                    let spans = self.merge(2, spans);
                    self.flush();
                    self.write(&load, spans);
                    return true;
                }
            }
            ([.., (I::I32Const(offset), _)], I::I32Add) if *offset > 0 => {
                self.held.push((I::I32Add, spans));
                if self.held.len() > 3 {
                    let (first, spans) = self.held.remove(0);
                    self.write(&first, spans);
                }
                return true;
            }
            ([.., (I::LocalSet(set), _)], I::LocalGet(get)) if set == get => {
                let local = *get;
                let spans = self.merge(1, spans);
                self.held.push((I::LocalTee(local), spans));
                self.flush();
                return true;
            }
            // A small constant-size copy is one load and one store. The load reads every byte
            // before the store writes, so overlapping ranges copy alike, and each traps where the
            // copy would, before writing anything.
            (
                [.., (I::I32Const(size), _)],
                I::MemoryCopy {
                    src_mem: 0,
                    dst_mem: 0,
                },
            ) => {
                if let Some((load, store)) = small_copy(*size) {
                    let spans = self.merge(1, spans);
                    self.instruction_from(&load, spans);
                    self.instruction_from(&store, spans);
                    return true;
                }
            }
            // A branch tests for non-zero, which a double negation preserves.
            ([.., (I::I32Eqz, _), (I::I32Eqz, _)], I::If(_) | I::BrIf(_)) => {
                let spans = self.merge(2, spans);
                self.flush();
                self.write(next, spans);
                return true;
            }
            _ => {}
        }
        self.flush();
        false
    }
}

/// An owned copy of an instruction a rewrite may involve.
#[inline(always)]
fn holdable(instruction: &I<'_>) -> Option<I<'static>> {
    Some(match instruction {
        I::I32Const(value) => I::I32Const(*value),
        I::I32Eqz => I::I32Eqz,
        I::LocalSet(local) => I::LocalSet(*local),
        comparison => complement(&complement(comparison)?)?,
    })
}

/// The comparison whose result is always the negation of `instruction`'s.
///
/// Ferlium floats have no NaN, so an ordered float comparison negates to the opposite ordered one.
#[inline(always)]
fn complement(instruction: &I<'_>) -> Option<I<'static>> {
    Some(match instruction {
        I::I32Eq => I::I32Ne,
        I::I32Ne => I::I32Eq,
        I::I32LtS => I::I32GeS,
        I::I32GeS => I::I32LtS,
        I::I32GtS => I::I32LeS,
        I::I32LeS => I::I32GtS,
        I::I32LtU => I::I32GeU,
        I::I32GeU => I::I32LtU,
        I::I32GtU => I::I32LeU,
        I::I32LeU => I::I32GtU,
        I::I64Eq => I::I64Ne,
        I::I64Ne => I::I64Eq,
        I::I64LtS => I::I64GeS,
        I::I64GeS => I::I64LtS,
        I::I64GtS => I::I64LeS,
        I::I64LeS => I::I64GtS,
        I::I64LtU => I::I64GeU,
        I::I64GeU => I::I64LtU,
        I::I64GtU => I::I64LeU,
        I::I64LeU => I::I64GtU,
        I::F64Eq => I::F64Ne,
        I::F64Ne => I::F64Eq,
        I::F64Lt => I::F64Ge,
        I::F64Ge => I::F64Lt,
        I::F64Gt => I::F64Le,
        I::F64Le => I::F64Gt,
        _ => return None,
    })
}

/// `load` reading `offset` bytes further, if it is a load whose static offset can take them.
///
/// `i32.add` wraps at 2³² where a static offset traps, so the two differ only when the address
/// sum leaves the 32-bit space. Emitted addresses never do: each is the start of a frame (checked
/// against the stack end on entry) or of an allocation, plus an offset within it, so the sum stays
/// below the end of linear memory. Should a compiler bug break this, the folded load traps where
/// the addition would silently have read low memory.
fn offset_load(load: &I<'_>, offset: u32) -> Option<I<'static>> {
    let moved = |memarg: &MemArg| {
        let offset = memarg.offset.checked_add(offset.into())?;
        (offset <= u32::MAX.into()).then_some(MemArg { offset, ..*memarg })
    };
    Some(match load {
        I::I32Load(memarg) => I::I32Load(moved(memarg)?),
        I::I64Load(memarg) => I::I64Load(moved(memarg)?),
        I::F32Load(memarg) => I::F32Load(moved(memarg)?),
        I::F64Load(memarg) => I::F64Load(moved(memarg)?),
        I::I32Load8S(memarg) => I::I32Load8S(moved(memarg)?),
        I::I32Load8U(memarg) => I::I32Load8U(moved(memarg)?),
        I::I32Load16S(memarg) => I::I32Load16S(moved(memarg)?),
        I::I32Load16U(memarg) => I::I32Load16U(moved(memarg)?),
        I::I64Load8S(memarg) => I::I64Load8S(moved(memarg)?),
        I::I64Load8U(memarg) => I::I64Load8U(moved(memarg)?),
        I::I64Load16S(memarg) => I::I64Load16S(moved(memarg)?),
        I::I64Load16U(memarg) => I::I64Load16U(moved(memarg)?),
        I::I64Load32S(memarg) => I::I64Load32S(moved(memarg)?),
        I::I64Load32U(memarg) => I::I64Load32U(moved(memarg)?),
        _ => return None,
    })
}

/// The load and store moving `size` bytes at once, if one scalar has that size.
///
/// The addresses' alignment is unknown here, so the access claims none; it only hints.
fn small_copy(size: i32) -> Option<(I<'static>, I<'static>)> {
    let memarg = MemArg {
        offset: 0,
        align: 0,
        memory_index: 0,
    };
    Some(match size {
        1 => (I::I32Load8U(memarg), I::I32Store8(memarg)),
        2 => (I::I32Load16U(memarg), I::I32Store16(memarg)),
        4 => (I::I32Load(memarg), I::I32Store(memarg)),
        8 => (I::I64Load(memarg), I::I64Store(memarg)),
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use wasm_bindgen_test::wasm_bindgen_test;
    use wasm_encoder::BlockType;

    use super::*;
    use crate::{Location, SourceId, mir::InlineSiteId};

    fn memarg(offset: u64) -> MemArg {
        MemArg {
            offset,
            align: 2,
            memory_index: 0,
        }
    }

    fn assert_rewrites(input: &[I<'_>], expected: &[I<'_>]) {
        let mut code = Code::new(WasmFunction::new([]));
        for instruction in input {
            code.instruction(instruction);
        }
        let mut function = WasmFunction::new([]);
        for instruction in expected {
            function.instruction(instruction);
        }
        assert_eq!(
            code.finish().0.into_raw_body(),
            function.into_raw_body(),
            "{input:?} must become {expected:?}"
        );
    }

    #[wasm_bindgen_test]
    fn negations_become_complements_and_zero_tests() {
        assert_rewrites(&[I::I32LtS, I::I32Eqz], &[I::I32GeS]);
        assert_rewrites(&[I::F64Gt, I::I32Const(0), I::I32Eq], &[I::F64Le]);
        assert_rewrites(&[I::I32Const(0), I::I32Eq], &[I::I32Eqz]);
        assert_rewrites(
            &[I::I32Eqz, I::I32Eqz, I::If(BlockType::Empty)],
            &[I::If(BlockType::Empty)],
        );
        // Without a branch, a double negation normalizes to 0 or 1 and must stay.
        assert_rewrites(
            &[I::I32Eqz, I::I32Eqz, I::Drop],
            &[I::I32Eqz, I::I32Eqz, I::Drop],
        );
    }

    #[wasm_bindgen_test]
    fn small_copies_become_a_load_and_a_store() {
        let copy = I::MemoryCopy {
            src_mem: 0,
            dst_mem: 0,
        };
        let unaligned = MemArg {
            offset: 0,
            align: 0,
            memory_index: 0,
        };
        assert_rewrites(
            &[I::I32Const(8), copy.clone()],
            &[I::I64Load(unaligned), I::I64Store(unaligned)],
        );
        // The source's constant offset moves into the load.
        assert_rewrites(
            &[I::I32Const(12), I::I32Add, I::I32Const(4), copy.clone()],
            &[
                I::I32Load(MemArg {
                    offset: 12,
                    ..unaligned
                }),
                I::I32Store(unaligned),
            ],
        );
        assert_rewrites(&[I::I32Const(16), copy.clone()], &[I::I32Const(16), copy]);
    }

    #[wasm_bindgen_test]
    fn read_back_sets_become_tees() {
        assert_rewrites(&[I::LocalSet(3), I::LocalGet(3)], &[I::LocalTee(3)]);
        assert_rewrites(
            &[I::LocalSet(3), I::LocalGet(4)],
            &[I::LocalSet(3), I::LocalGet(4)],
        );
    }

    #[wasm_bindgen_test]
    fn rewrites_keep_the_sources_of_what_they_merge() {
        let span = |start| DebugLocation::new(Location::new(start, start + 1, SourceId::new(1)));
        let sources = |input: &[(Option<DebugLocation>, I<'_>)]| {
            let mut code = Code::new(WasmFunction::new([]));
            for (source, instruction) in input {
                code.set_source(*source);
                code.instruction(instruction);
            }
            code.finish()
                .1
                .into_iter()
                .map(|(_, span)| span)
                .collect::<Vec<_>>()
        };
        let (a, b) = (span(1), span(2));
        // A set read back by other code: the tee does the work of both.
        assert_eq!(
            sources(&[(Some(a), I::LocalSet(3)), (Some(b), I::LocalGet(3))]),
            [a, b]
        );
        // A comparison negated by other code, and a comparison with zero.
        assert_eq!(
            sources(&[(Some(a), I::I32LtS), (Some(b), I::I32Eqz)]),
            [a, b]
        );
        assert_eq!(
            sources(&[(Some(a), I::I32Const(0)), (Some(b), I::I32Eq)]),
            [a, b]
        );
        // Code without a source contributes none, and adjacent code of one source is one range.
        assert_eq!(
            sources(&[
                (Some(a), I::LocalGet(0)),
                (Some(a), I::LocalGet(1)),
                (None, I::Drop),
                (Some(b), I::LocalSet(2)),
            ]),
            [a, b]
        );
        // One source inlined at two call sites is two sources.
        let inlined = |site| DebugLocation {
            inlined_at: Some(InlineSiteId::new(site)),
            ..a
        };
        assert_eq!(
            sources(&[
                (Some(inlined(0)), I::LocalSet(3)),
                (Some(inlined(1)), I::LocalGet(3))
            ]),
            [inlined(0), inlined(1)]
        );
    }

    #[wasm_bindgen_test]
    fn constant_offsets_fold() {
        assert_rewrites(&[I::I32Const(0), I::I32Add], &[]);
        assert_rewrites(
            &[I::I32Const(4), I::I32Add, I::I32Const(8), I::I32Add],
            &[I::I32Const(12), I::I32Add],
        );
        assert_rewrites(
            &[I::I32Const(4), I::I32Add, I::I32Const(-4), I::I32Add],
            &[],
        );
        assert_rewrites(
            &[I::I32Const(4), I::I32Add, I::I32Load(memarg(8))],
            &[I::I32Load(memarg(12))],
        );
        assert_rewrites(
            &[
                I::I32Const(4),
                I::I32Add,
                I::I32Const(8),
                I::I32Add,
                I::F64Load(memarg(0)),
            ],
            &[I::F64Load(memarg(12))],
        );
        // A negative offset or one beyond the static range stays an addition.
        for (offset, load) in [(-4, 8), (4, u64::from(u32::MAX))] {
            assert_rewrites(
                &[I::I32Const(offset), I::I32Add, I::I32Load(memarg(load))],
                &[I::I32Const(offset), I::I32Add, I::I32Load(memarg(load))],
            );
        }
    }
}
