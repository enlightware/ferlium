// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Local rewrites of adjacent instructions while a function body is emitted.

use wasm_encoder::{Function as WasmFunction, Instruction as I, MemArg};

/// Where emitted instructions go: straight into a function, or through [`Code`]'s rewrites.
pub(super) trait Instructions {
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

/// A function body under construction that holds back its last few instructions, so that a
/// negated comparison becomes the complementary one, a comparison with zero a zero test, a set
/// read back a tee, constant additions one or none, and a constant address offset part of its
/// load.
///
/// Held instructions are written out before any other access, so bytes already written never
/// change: byte offsets taken for the source map stay valid. The exception is a trailing
/// `local.set`, counted as written, as it can only become a `local.tee` of the same length. Only a
/// branch sees what is held, and nothing is held across it.
pub(super) struct Code {
    function: WasmFunction,
    held: Vec<I<'static>>,
}

impl Code {
    pub(super) fn new(function: WasmFunction) -> Self {
        Self {
            function,
            held: Vec::new(),
        }
    }

    /// The function with every held instruction written.
    pub(super) fn function(&mut self) -> &mut WasmFunction {
        for instruction in self.held.drain(..) {
            self.function.instruction(&instruction);
        }
        &mut self.function
    }

    /// The length of the code so far, counting a trailing held `local.set`, which may still become
    /// a `local.tee` of the same length, so that a source region may end on it.
    pub(super) fn byte_len(&mut self) -> usize {
        let Some(&I::LocalSet(local)) = self.held.last() else {
            return self.function().byte_len();
        };
        let set = self.held.pop().expect("a held instruction is last");
        let length = self.function().byte_len();
        self.held.push(set);
        length + 1 + leb128_length(local)
    }

    pub(super) fn finish(mut self) -> WasmFunction {
        self.function();
        self.function
    }

    /// Inlined, so that a call site's known instruction selects its path and encoding statically.
    #[inline(always)]
    pub(super) fn instruction(&mut self, instruction: &I<'_>) {
        if let Some(instruction) = holdable(instruction) {
            self.hold(instruction);
        } else if self.held.is_empty() || !self.release(instruction) {
            self.function.instruction(instruction);
        }
    }

    #[inline(never)]
    fn hold(&mut self, instruction: I<'static>) {
        self.held.push(instruction);
        loop {
            match self.held.as_slice() {
                // `x == 0` is `x.eqz`.
                [.., I::I32Const(0), I::I32Eq] => {
                    self.held.truncate(self.held.len() - 2);
                    self.held.push(I::I32Eqz);
                }
                // A comparison yields 0 or 1, so its negation is the complementary comparison.
                [.., comparison, I::I32Eqz] => {
                    let Some(complement) = complement(comparison) else {
                        break;
                    };
                    self.held.truncate(self.held.len() - 2);
                    self.held.push(complement);
                }
                _ => break,
            }
        }
        if self.held.len() > 3 {
            let first = self.held.remove(0);
            self.function.instruction(&first);
        }
    }

    /// Writes the held instructions before `next`, or absorbs `next` into them, returning whether
    /// it did.
    #[inline(never)]
    fn release(&mut self, next: &I<'_>) -> bool {
        match (self.held.as_slice(), next) {
            // Adding zero changes nothing; the rest stays held.
            ([.., I::I32Const(0)], I::I32Add) => {
                self.held.pop();
                return true;
            }
            // Constant additions combine, as both wrap.
            ([.., I::I32Const(first), I::I32Add, I::I32Const(second)], I::I32Add) => {
                let sum = first.wrapping_add(*second);
                self.held.truncate(self.held.len() - 3);
                if sum != 0 {
                    self.held.extend([I::I32Const(sum), I::I32Add]);
                }
                return true;
            }
            // A constant address offset may move into a load's static offset.
            ([.., I::I32Const(offset), I::I32Add], _) if *offset > 0 => {
                if let Some(load) = offset_load(next, *offset as u32) {
                    self.held.truncate(self.held.len() - 2);
                    self.function();
                    self.function.instruction(&load);
                    return true;
                }
            }
            ([.., I::I32Const(offset)], I::I32Add) if *offset > 0 => {
                self.held.push(I::I32Add);
                if self.held.len() > 3 {
                    let first = self.held.remove(0);
                    self.function.instruction(&first);
                }
                return true;
            }
            ([.., I::LocalSet(set)], I::LocalGet(get)) if set == get => {
                let local = *get;
                self.held.pop();
                self.held.push(I::LocalTee(local));
                self.function();
                return true;
            }
            // A branch tests for non-zero, which a double negation preserves.
            ([.., I::I32Eqz, I::I32Eqz], I::If(_) | I::BrIf(_)) => {
                self.held.truncate(self.held.len() - 2);
            }
            _ => {}
        }
        self.function();
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

/// The encoded length of `value` as an unsigned LEB128 integer.
fn leb128_length(value: u32) -> usize {
    (32 - value.leading_zeros() as usize).max(1).div_ceil(7)
}

#[cfg(test)]
mod tests {
    use wasm_bindgen_test::wasm_bindgen_test;
    use wasm_encoder::BlockType;

    use super::*;

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
            code.finish().into_raw_body(),
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
    fn read_back_sets_become_tees() {
        assert_rewrites(&[I::LocalSet(3), I::LocalGet(3)], &[I::LocalTee(3)]);
        assert_rewrites(
            &[I::LocalSet(3), I::LocalGet(4)],
            &[I::LocalSet(3), I::LocalGet(4)],
        );
    }

    #[wasm_bindgen_test]
    fn a_held_set_counts_towards_the_length_it_keeps_as_a_tee() {
        let mut code = Code::new(WasmFunction::new([]));
        code.instruction(&I::LocalSet(200));
        let length = code.byte_len();
        code.instruction(&I::LocalGet(200));
        assert_eq!(code.byte_len(), length);
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
