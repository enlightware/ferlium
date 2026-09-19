// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Relocatable immutable evidence data and the runtime ownership of captured environments.

use std::{mem::offset_of, ptr};

#[cfg(test)]
use std::cell::Cell;

use crate::{
    FxHashMap, FxHashSet,
    mir::{
        Value,
        physical::{
            DictionaryReference, EvidenceEnvironmentLayout,
            program::{InternedStaticEvidence, ProgramEvidenceId, ResolvedPhysicalProgram},
        },
    },
    module::{TraitDictionaryId, TraitId, id::Id},
    types::r#trait::TraitDictionaryEntryIndex,
};

use super::{abi::DispatchTableSlotId, runtime};

/// Descriptor offsets are relative to the instance's immutable data base; table entries are local.
#[repr(C)]
pub(super) struct DictionaryDescriptor {
    pub size: u32,
    pub align: u32,
    pub captures: u32,
    pub entries: u32,
}

/// One reachable evidence graph, shared by all users rather than duplicated at each call site.
#[derive(Default)]
pub(super) struct ReachableEvidence {
    pub dictionaries: Vec<TraitDictionaryId>,
    pub entries: Vec<(TraitId, TraitDictionaryEntryIndex)>,
    pub statics: Vec<ProgramEvidenceId>,
    dictionary_set: FxHashSet<TraitDictionaryId>,
    entry_set: FxHashSet<(TraitId, TraitDictionaryEntryIndex)>,
    static_set: FxHashSet<ProgramEvidenceId>,
    dispatched_dictionaries: usize,
    dispatched_entries: usize,
    dictionaries_by_trait: FxHashMap<TraitId, Vec<TraitDictionaryId>>,
    entries_by_trait: FxHashMap<TraitId, Vec<TraitDictionaryEntryIndex>>,
}

impl ReachableEvidence {
    /// Visit each reachable dictionary/entry pair once, including pairs discovered by callees.
    pub fn discover_dispatches(
        &mut self,
        program: &ResolvedPhysicalProgram<'_>,
        mut visit: impl FnMut(TraitDictionaryId, TraitDictionaryEntryIndex),
    ) {
        for &id in &self.dictionaries[self.dispatched_dictionaries..] {
            let trait_id = program.dictionary(id).unwrap().trait_id();
            if let Some(entries) = self.entries_by_trait.get(&trait_id) {
                for &entry in entries {
                    visit(id, entry);
                }
            }
            self.dictionaries_by_trait
                .entry(trait_id)
                .or_default()
                .push(id);
        }
        for &(trait_id, entry) in &self.entries[self.dispatched_entries..] {
            if let Some(dictionaries) = self.dictionaries_by_trait.get(&trait_id) {
                for &id in dictionaries {
                    visit(id, entry);
                }
            }
            self.entries_by_trait
                .entry(trait_id)
                .or_default()
                .push(entry);
        }
        self.dispatched_dictionaries = self.dictionaries.len();
        self.dispatched_entries = self.entries.len();
    }

    pub fn dictionary(&mut self, id: TraitDictionaryId) {
        if self.dictionary_set.insert(id) {
            self.dictionaries.push(id);
        }
    }

    pub fn entry(&mut self, id: TraitId, entry: TraitDictionaryEntryIndex) {
        if self.entry_set.insert((id, entry)) {
            self.entries.push((id, entry));
        }
    }

    pub fn value(
        &mut self,
        program: &ResolvedPhysicalProgram<'_>,
        value: &Value,
    ) -> Result<(), String> {
        if let Some(id) = program.evidence_id(value) {
            self.static_value(program, id)?;
        }
        Ok(())
    }

    fn static_value(
        &mut self,
        program: &ResolvedPhysicalProgram<'_>,
        id: ProgramEvidenceId,
    ) -> Result<(), String> {
        if !self.static_set.insert(id) {
            return Ok(());
        }
        match &program.static_evidence()[id.as_index()] {
            InternedStaticEvidence::Dictionary {
                definition,
                captures,
            } => {
                self.dictionary(*definition);
                for &capture in captures {
                    self.static_value(program, capture)?;
                }
            }
            InternedStaticEvidence::VariantPayloadStorage(_) => (),
            InternedStaticEvidence::Subscript { .. } => {
                return Err("static subscript evidence".into());
            }
        }
        self.statics.push(id); // Children precede their immutable parents.
        Ok(())
    }
}

/// Address-independent data. Only pointer fields are relocated when creating an instance.
#[derive(Default)]
pub(super) struct Image {
    words: Vec<u32>,
    relocations: Vec<usize>,
    pub references: FxHashMap<ProgramEvidenceId, u32>,
}

impl Image {
    /// Append one immutable captureless callable; discovery interns these by function identity.
    pub fn callable_reference(&mut self, slot: DispatchTableSlotId) -> u32 {
        let offset = self.words.len() as u32 * 4;
        self.words.extend([slot.as_u32(), 0]);
        offset
    }

    pub fn build(
        program: &ResolvedPhysicalProgram<'_>,
        reachable: &ReachableEvidence,
        table: &FxHashMap<(TraitDictionaryId, usize), DispatchTableSlotId>,
    ) -> Self {
        let count = reachable
            .dictionaries
            .iter()
            .map(|id| program.descriptor_index(*id).unwrap().as_index() + 1)
            .max()
            .unwrap_or(0);
        let mut this = Self {
            words: vec![0; count],
            ..Self::default()
        };
        for &id in &reachable.dictionaries {
            let definition = program.dictionary(id).unwrap();
            let layout = definition.environment();
            let descriptor = this.words.len() * 4;
            this.words[program.descriptor_index(id).unwrap().as_index()] = descriptor as u32;
            let entries = descriptor + size_of::<DictionaryDescriptor>() + layout.fields.len() * 4;
            this.words.extend([
                layout.allocation.size() as u32,
                layout.allocation.align() as u32,
                layout.fields.len() as u32,
                entries as u32,
            ]);
            this.words.extend(layout.fields.iter().map(|field| {
                field.offset as u32 | if field.is_storage_flag { 1 << 31 } else { 0 }
            }));
            this.words.extend(
                (0..definition.entries().len())
                    .map(|index| table.get(&(id, index)).map_or(0, |slot| slot.as_u32())),
            );
        }
        for &id in &reachable.statics {
            let offset = match &program.static_evidence()[id.as_index()] {
                InternedStaticEvidence::VariantPayloadStorage(value) => {
                    let offset = this.words.len() * 4;
                    this.words.push(u32::from(*value));
                    offset
                }
                InternedStaticEvidence::Dictionary {
                    definition,
                    captures,
                } => {
                    let layout = program.dictionary(*definition).unwrap().environment();
                    let captures = captures
                        .iter()
                        .map(|id| this.references[id])
                        .collect::<Vec<_>>();
                    this.dictionary(
                        program.descriptor_index(*definition).unwrap().as_u32(),
                        layout,
                        &captures,
                    )
                }
                InternedStaticEvidence::Subscript { .. } => unreachable!(),
            };
            this.references.insert(id, offset as u32);
        }
        this
    }

    fn dictionary(
        &mut self,
        descriptor: u32,
        layout: &EvidenceEnvironmentLayout,
        captures: &[u32],
    ) -> usize {
        let environment = if captures.is_empty() {
            0
        } else {
            let start = self.words.len();
            self.words
                .resize(start + layout.allocation.size().div_ceil(4), 0);
            for (field, source) in layout.fields.iter().zip(captures) {
                let source = *source as usize / 4;
                let target = start + field.offset / 4;
                if field.is_storage_flag {
                    // Several one-byte flags can occupy the same word.
                    self.words[target] |= self.words[source] << (8 * (field.offset % 4));
                } else {
                    self.words[target] = self.words[source];
                    self.words[target + 1] = self.words[source + 1];
                    if self.words[target + 1] != 0 {
                        self.relocations.push(target + 1);
                    }
                }
            }
            start * 4
        };
        let offset = self.words.len() * 4;
        self.words.extend([descriptor, environment as u32]);
        if environment != 0 {
            self.relocations.push(offset / 4 + 1);
        }
        offset
    }

    pub fn instantiate(&self) -> Box<[u32]> {
        let mut data = self.words.clone().into_boxed_slice();
        let base = data.as_ptr() as u32;
        for &index in &self.relocations {
            data[index] += base;
        }
        data
    }
}

unsafe fn descriptor<'a>(data: *const u8, index: u32) -> &'a DictionaryDescriptor {
    // SAFETY: generated references use a descriptor in this instance's live immutable image.
    unsafe {
        &*data
            .add(data.cast::<u32>().add(index as usize).read() as usize)
            .cast()
    }
}

/// # Safety
/// The reference and its immutable environment must be live for this call.
pub(super) unsafe extern "C" fn retain(reference: *const DictionaryReference) {
    // SAFETY: the caller borrows a valid reference; nonzero environments start with a refcount.
    unsafe {
        let environment = (*reference).environment as *mut usize;
        if !environment.is_null() && environment.read() != 0 {
            environment.write(
                environment
                    .read()
                    .checked_add(1)
                    .expect("evidence reference count overflow"),
            );
        }
    }
}

/// # Safety
/// The reference owns one share of its environment, described by this instance's data image.
pub(super) unsafe extern "C" fn release(data: *const u8, reference: *const DictionaryReference) {
    // SAFETY: ownership is supplied by the caller; captures remain live until their owner is freed.
    unsafe {
        let reference = reference.read();
        let environment = reference.environment as *mut usize;
        if environment.is_null() || environment.read() == 0 {
            return;
        }
        let count = environment.read() - 1;
        environment.write(count);
        if count != 0 {
            return;
        }
        let descriptor = descriptor(data, reference.descriptor);
        let fields = ptr::from_ref(descriptor)
            .byte_add(size_of::<DictionaryDescriptor>())
            .cast::<u32>();
        for index in 0..descriptor.captures as usize {
            let field = fields.add(index).read();
            if field & (1 << 31) == 0 {
                release(data, environment.byte_add(field as usize).cast());
            }
        }
        runtime::release(environment.cast());
        #[cfg(test)]
        LIVE_ENVIRONMENTS.set(LIVE_ENVIRONMENTS.get() - 1);
    }
}

/// # Safety
/// Captures use the descriptor's layout and remain borrowed until this call returns. Output is absent.
pub(super) unsafe extern "C" fn build(
    data: *const u8,
    index: u32,
    captures: *const u8,
    output: *mut DictionaryReference,
) {
    // SAFETY: the generated caller fills every capture field according to the retained schema.
    unsafe {
        let descriptor = descriptor(data, index);
        let environment = if descriptor.captures == 0 {
            ptr::null_mut()
        } else {
            let environment =
                runtime::allocate(descriptor.size as usize, descriptor.align as usize);
            ptr::copy_nonoverlapping(captures, environment, descriptor.size as usize);
            environment.cast::<usize>().write(1);
            let fields = ptr::from_ref(descriptor)
                .byte_add(size_of::<DictionaryDescriptor>())
                .cast::<u32>();
            for index in 0..descriptor.captures as usize {
                let field = fields.add(index).read();
                if field & (1 << 31) == 0 {
                    retain(environment.add(field as usize).cast());
                }
            }
            #[cfg(test)]
            {
                LIVE_ENVIRONMENTS.set(LIVE_ENVIRONMENTS.get() + 1);
                BUILT_ENVIRONMENTS.set(BUILT_ENVIRONMENTS.get() + 1);
            }
            environment
        };
        output.write(DictionaryReference {
            descriptor: index,
            environment: environment as usize,
        });
    }
}

pub(super) const ENVIRONMENT_OFFSET: u64 = offset_of!(DictionaryReference, environment) as u64;

#[cfg(test)]
thread_local! {
    pub(super) static LIVE_ENVIRONMENTS: Cell<usize> = const { Cell::new(0) };
    pub(super) static BUILT_ENVIRONMENTS: Cell<usize> = const { Cell::new(0) };
}

#[cfg(test)]
mod tests {
    use wasm_bindgen_test::wasm_bindgen_test;

    use super::super::{Imports, codegen_tests::with_raw_program, emit};
    use crate::{
        CompilerSession, FxHashSet, MirOptimization,
        module::{FunctionId, Path, id::Id},
        types::r#trait::TraitDictionaryEntryIndex,
        ustr,
    };

    use super::ReachableEvidence;

    #[wasm_bindgen_test]
    fn wasm_codegen_static_evidence_image() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Disabled);
        session.set_physical_mir_optimization(MirOptimization::Disabled);
        let module = session.compile(
            "#[inline(never)] fn duplicate<T>(x: T) -> (T, T) { (x, x) } fn compute(x: int) -> int { let p = duplicate((x, (true, x))); p.0.0 + p.1.0 }",
            "image", Path::single_str("image"),
        ).unwrap().module_id;
        let entry = FunctionId::new(
            module,
            session
                .expect_fresh_module(module)
                .get_local_function_id(ustr("compute"))
                .unwrap(),
        );
        with_raw_program(&session, entry, |program| {
            let emitted =
                emit::emit(program, entry, &mut Imports::new().unwrap(), &session).unwrap();
            let again = emit::emit(program, entry, &mut Imports::new().unwrap(), &session).unwrap();
            assert_eq!(emitted.bytes, again.bytes);
            assert_eq!(emitted.evidence.words, again.evidence.words);
            let image = emitted.evidence;
            assert!(!image.references.is_empty());
            let first = image.instantiate();
            let second = image.instantiate();
            assert_ne!(first.as_ptr(), second.as_ptr());
            for &index in &image.relocations {
                let offset = image.words[index];
                assert!((offset as usize) < image.words.len() * size_of::<u32>());
                assert_eq!(first[index], first.as_ptr() as u32 + offset);
                assert_eq!(second[index], second.as_ptr() as u32 + offset);
            }
            // Each program identity has exactly one emitted reference, regardless of its uses.
            let mut reachable = super::ReachableEvidence::default();
            for &id in image.references.keys() {
                reachable.static_value(program, id).unwrap();
                let count = reachable.statics.len();
                reachable.static_value(program, id).unwrap();
                assert_eq!(reachable.statics.len(), count);
            }
            assert_eq!(reachable.statics.len(), image.references.len());

            // Grow the two sides in opposite orders. Every compatible pair must be discovered
            // exactly once, even when another dispatch introduces dictionaries or entry uses.
            let dictionaries: Vec<_> = program
                .modules()
                .iter()
                .flat_map(|module| module.dictionaries())
                .filter(|definition| definition.entries().len() > 1)
                .map(|definition| definition.id())
                .collect();
            assert!(
                dictionaries.len() > 1,
                "fixture needs several multi-entry dictionaries"
            );
            let first_entry = TraitDictionaryEntryIndex::from_index(0);
            let second_entry = TraitDictionaryEntryIndex::from_index(1);
            let mut incremental = ReachableEvidence::default();
            let mut dispatched = Vec::new();
            for (index, &id) in dictionaries.iter().enumerate() {
                let definition = program.dictionary(id).unwrap();
                if index % 2 == 0 {
                    incremental.entry(definition.trait_id(), first_entry);
                }
                incremental.dictionary(id);
                incremental.discover_dispatches(program, |id, entry| dispatched.push((id, entry)));
                incremental.entry(definition.trait_id(), first_entry);
                incremental.entry(definition.trait_id(), second_entry);
                incremental.discover_dispatches(program, |id, entry| dispatched.push((id, entry)));
                incremental.discover_dispatches(program, |_, _| panic!("dispatch visited twice"));
            }
            let expected: FxHashSet<_> = dictionaries
                .iter()
                .flat_map(|&id| [(id, first_entry), (id, second_entry)])
                .collect();
            assert_eq!(dispatched.len(), expected.len());
            assert_eq!(dispatched.into_iter().collect::<FxHashSet<_>>(), expected);
        });
    }

    #[wasm_bindgen_test]
    fn wasm_codegen_nested_static_evidence_relocations() {
        use super::{EvidenceEnvironmentLayout, Image};
        // Two adjacent boolean captures and two references sharing one nested static environment.
        let mut image = Image {
            words: vec![0, 1],
            ..Image::default()
        };
        let leaf = image.dictionary(0, &EvidenceEnvironmentLayout::new([]).unwrap(), &[]) as u32;
        let inner_layout = EvidenceEnvironmentLayout::new([true, true, false]).unwrap();
        let inner = image.dictionary(1, &inner_layout, &[0, 4, leaf]) as u32;
        let outer_layout = EvidenceEnvironmentLayout::new([false, false]).unwrap();
        let outer = image.dictionary(2, &outer_layout, &[inner, inner]);
        assert!(!image.relocations.is_empty());
        for data in [image.instantiate(), image.instantiate()] {
            let base = data.as_ptr() as u32;
            for &index in &image.relocations {
                assert_eq!(data[index], base + image.words[index]);
            }
            let inner_env = image.words[inner as usize / 4 + 1] as usize / 4;
            assert_eq!(data[inner_env], 0, "static reference count");
            assert_eq!(data[inner_env + inner_layout.fields[0].offset / 4], 256);
            let outer_env = image.words[outer / 4 + 1] as usize / 4;
            for field in outer_layout.fields.iter() {
                assert_eq!(
                    data[outer_env + field.offset / 4 + 1],
                    base + (inner_env * 4) as u32
                );
            }
        }
    }
}
