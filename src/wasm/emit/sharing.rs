// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Share encoded implementations after all function-index dependencies are visible.

use std::{ops::Range, rc::Rc};

use wasm_encoder::{
    CodeSection, Encode, ExportKind, ExportSection, FunctionSection, Module, NameMap, NameSection,
    RawSection,
};
use wasmparser::{
    BinaryReader, ElementItems, ElementKind, ExternalKind, FunctionBody, Name, NameSectionReader,
    Operator, OperatorsReader, Parser, Payload, TableInit, TypeRef,
};

use crate::{
    FxHashMap,
    graph::{self, Node},
};

use super::{CodeSourceMapEntry, merge_function_source_maps};

struct Relocation {
    bytes: Range<usize>,
    function: u32,
}

struct Body {
    ty: u32,
    bytes: Rc<[u8]>,
    relocations: Vec<Relocation>,
    dependencies: Vec<usize>,
}

impl Node for Body {
    type Index = usize;
    fn neighbors(&self) -> impl Iterator<Item = usize> {
        self.dependencies.iter().copied()
    }
}

fn references(mut reader: OperatorsReader<'_>, base: usize) -> Result<Vec<Relocation>, String> {
    let mut relocations = Vec::new();
    while !reader.eof() {
        let start = reader.original_position() as usize;
        let operator = reader.read().map_err(|error| error.to_string())?;
        if let Operator::Call { function_index }
        | Operator::ReturnCall { function_index }
        | Operator::RefFunc { function_index } = operator
        {
            // Each of these has one single-byte opcode followed by a function-index LEB.
            relocations.push(Relocation {
                bytes: start + 1 - base..reader.original_position() as usize - base,
                function: function_index,
            });
        }
    }
    Ok(relocations)
}

/// Patch only function-index immediates, preserving every other encoded byte. The boundary shifts
/// let debug ranges follow changes in LEB width; instruction boundaries never split an immediate.
fn relocate(
    bytes: &Rc<[u8]>,
    relocations: &[Relocation],
    indices: &[u32],
) -> (Rc<[u8]>, Vec<(usize, isize)>) {
    if relocations
        .iter()
        .all(|relocation| indices[relocation.function as usize] == relocation.function)
    {
        return (bytes.clone(), Vec::new());
    }
    let mut output = Vec::with_capacity(bytes.len());
    let mut cursor = 0;
    let mut shifts = Vec::new();
    let mut shift = 0;
    for relocation in relocations {
        output.extend_from_slice(&bytes[cursor..relocation.bytes.start]);
        indices[relocation.function as usize].encode(&mut output);
        cursor = relocation.bytes.end;
        let next_shift = output.len() as isize - cursor as isize;
        if next_shift != shift {
            shift = next_shift;
            shifts.push((cursor, shift));
        }
    }
    output.extend_from_slice(&bytes[cursor..]);
    (output.into(), shifts)
}

fn root(indices: &[u32], mut index: u32) -> u32 {
    while indices[index as usize] != index {
        index = indices[index as usize];
    }
    index
}

/// Types are already interned by the emitter, so a type index identifies the complete signature.
/// Process dependencies first. Only recursive components need local folding rounds; internal
/// function identities stay distinct unless an exact match proves a merge, not graph isomorphism.
pub(in crate::wasm) fn share(
    bytes: Vec<u8>,
    source_map: Vec<CodeSourceMapEntry>,
) -> Result<(Vec<u8>, Vec<CodeSourceMapEntry>), String> {
    let mut imported = 0;
    let mut types = Vec::new();
    let mut bodies = Vec::new();
    for payload in Parser::new(0).parse_all(&bytes) {
        match payload.map_err(|error| error.to_string())? {
            Payload::ImportSection(section) => {
                for import in section.into_imports() {
                    if matches!(
                        import.map_err(|error| error.to_string())?.ty,
                        TypeRef::Func(_) | TypeRef::FuncExact(_)
                    ) {
                        imported += 1;
                    }
                }
            }
            Payload::FunctionSection(section) => {
                types = section
                    .into_iter()
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|error| error.to_string())?;
            }
            Payload::CodeSectionEntry(body) => {
                let raw = Rc::<[u8]>::from(body.as_bytes());
                let body = FunctionBody::new(BinaryReader::new(&raw, 0));
                let relocations = references(
                    body.get_operators_reader()
                        .map_err(|error| error.to_string())?,
                    0,
                )?;
                let mut dependencies = relocations
                    .iter()
                    .filter_map(|relocation| (relocation.function as usize).checked_sub(imported))
                    .collect::<Vec<_>>();
                dependencies.sort_unstable();
                dependencies.dedup();
                bodies.push(Body {
                    ty: types[bodies.len()],
                    bytes: raw,
                    relocations,
                    dependencies,
                });
            }
            _ => {}
        }
    }
    let count = imported + bodies.len();
    let mut canonical = (0..count as u32).collect::<Vec<_>>();
    let components = graph::find_strongly_connected_components(&bodies);
    let mut keys = FxHashMap::default();
    for mut component in graph::topological_sort_sccs(&bodies, &components)
        .into_iter()
        .rev()
    {
        if let [body] = component.as_slice() {
            // A singleton cannot discover local aliases, even when it references itself.
            let index = (imported + body) as u32;
            let body = &bodies[*body];
            let normalized = relocate(&body.bytes, &body.relocations, &canonical).0;
            canonical[index as usize] = *keys.entry((body.ty, normalized)).or_insert(index);
            continue;
        }
        component.sort_unstable();
        loop {
            let mut local_keys = FxHashMap::default();
            let candidates = component
                .iter()
                .filter_map(|&body| {
                    let index = (imported + body) as u32;
                    (root(&canonical, index) == index).then(|| {
                        let body = &bodies[body];
                        let normalized = relocate(&body.bytes, &body.relocations, &canonical).0;
                        (index, (body.ty, normalized))
                    })
                })
                .collect::<Vec<_>>();
            let mut merged = false;
            for (index, key) in candidates {
                if let Some(&existing) = keys.get(&key).or_else(|| local_keys.get(&key)) {
                    canonical[index as usize] = existing;
                    merged = true;
                } else {
                    local_keys.insert(key, index);
                }
            }
            for &body in &component {
                let index = imported + body;
                canonical[index] = root(&canonical, index as u32);
            }
            if !merged {
                keys.extend(local_keys);
                break;
            }
        }
    }
    if canonical
        .iter()
        .enumerate()
        .all(|(index, &canonical)| index as u32 == canonical)
    {
        return Ok((bytes, source_map));
    }
    let kept = (imported..count)
        .filter(|&index| canonical[index] == index as u32)
        .collect::<Vec<_>>();
    let mut indices = (0..count as u32).collect::<Vec<_>>();
    let mut origins = vec![Vec::new(); count];
    for index in imported..count {
        origins[canonical[index] as usize].push(index);
    }
    for (body, &index) in kept.iter().enumerate() {
        indices[index] = (imported + body) as u32;
    }
    for index in imported..count {
        indices[index] = indices[canonical[index] as usize];
    }
    let mut shifts = Vec::new();
    let mut mapped_sources = vec![Vec::new(); kept.len()];
    if !source_map.is_empty() {
        for body in &bodies {
            shifts.push(relocate(&body.bytes, &body.relocations, &indices).1);
        }
    }
    for mut entry in source_map {
        let body = entry.body;
        let shift = |position| {
            let preceding = shifts[body].partition_point(|&(end, _)| end <= position);
            position
                .checked_add_signed(
                    preceding
                        .checked_sub(1)
                        .map_or(0, |index| shifts[body][index].1),
                )
                .expect("relocated source offset")
        };
        entry.bytes = shift(entry.bytes.start)..shift(entry.bytes.end);
        entry.body = indices[imported + body] as usize - imported;
        mapped_sources[entry.body].push(entry);
    }
    let mut output_sources = Vec::new();
    for (body, entries) in mapped_sources.into_iter().enumerate() {
        if origins[kept[body]].len() > 1 {
            output_sources.extend(merge_function_source_maps(entries));
        } else {
            output_sources.extend(entries);
        }
    }
    let mut module = Module::new();
    for payload in Parser::new(0).parse_all(&bytes) {
        let payload = payload.map_err(|error| error.to_string())?;
        match payload {
            Payload::FunctionSection(_) => {
                let mut section = FunctionSection::new();
                for &index in &kept {
                    section.function(bodies[index - imported].ty);
                }
                module.section(&section);
            }
            Payload::CodeSectionStart { .. } => {
                let mut section = CodeSection::new();
                for &index in &kept {
                    let body = &bodies[index - imported];
                    section.raw(&relocate(&body.bytes, &body.relocations, &indices).0);
                }
                module.section(&section);
            }
            Payload::CodeSectionEntry(_) => {}
            Payload::ExportSection(section) => {
                let mut output = ExportSection::new();
                for export in section {
                    let export = export.map_err(|error| error.to_string())?;
                    let (kind, index) = match export.kind {
                        ExternalKind::Func | ExternalKind::FuncExact => {
                            (ExportKind::Func, indices[export.index as usize])
                        }
                        ExternalKind::Table => (ExportKind::Table, export.index),
                        ExternalKind::Memory => (ExportKind::Memory, export.index),
                        ExternalKind::Global => (ExportKind::Global, export.index),
                        ExternalKind::Tag => (ExportKind::Tag, export.index),
                    };
                    output.export(export.name, kind, index);
                }
                module.section(&output);
            }
            Payload::StartSection { func, .. } => {
                module.section(&wasm_encoder::StartSection {
                    function_index: indices[func as usize],
                });
            }
            Payload::CustomSection(section) if section.name() == "name" => {
                let mut names = vec![String::new(); count];
                let mut globals = NameMap::new();
                for name in NameSectionReader::new(section.data_reader()) {
                    match name.map_err(|error| error.to_string())? {
                        Name::Function(map) => {
                            for name in map {
                                let name = name.map_err(|error| error.to_string())?;
                                names[name.index as usize] = name.name.to_owned();
                            }
                        }
                        Name::Global(map) => {
                            for name in map {
                                let name = name.map_err(|error| error.to_string())?;
                                globals.append(name.index, name.name);
                            }
                        }
                        _ => return Err("Wasm sharing: unsupported emitted name subsection".into()),
                    }
                }
                let mut functions = NameMap::new();
                for (index, name) in names.iter().enumerate().take(imported) {
                    functions.append(index as u32, name);
                }
                for &index in &kept {
                    let name = &names[origins[index][0]];
                    if origins[index].len() > 1 {
                        functions.append(
                            indices[index],
                            &format!(
                                "<shared function {} ×{}>",
                                name.strip_prefix('<')
                                    .and_then(|name| name.strip_suffix('>'))
                                    .unwrap_or(name),
                                origins[index].len()
                            ),
                        );
                    } else {
                        functions.append(indices[index], name);
                    }
                }
                let mut section = NameSection::new();
                section.functions(&functions);
                section.globals(&globals);
                module.section(&section);
            }
            Payload::CustomSection(section) => {
                // Offset-sensitive debug metadata must be built after sharing, not copied stale.
                return Err(format!(
                    "Wasm sharing: unsupported emitted custom section {}",
                    section.name()
                ));
            }
            _ => {
                if let Some((id, range)) = payload.as_section() {
                    let mut relocations = Vec::new();
                    match &payload {
                        Payload::ElementSection(section) => {
                            for element in section.clone() {
                                let element = element.map_err(|error| error.to_string())?;
                                if let ElementKind::Active { offset_expr, .. } = element.kind {
                                    relocations.extend(references(
                                        offset_expr.get_operators_reader(),
                                        range.start as usize,
                                    )?);
                                }
                                match element.items {
                                    ElementItems::Functions(items) => {
                                        for item in items.into_iter_with_offsets() {
                                            let (offset, function) =
                                                item.map_err(|error| error.to_string())?;
                                            // This stage consumes wasm-encoder output, which uses
                                            // the shortest LEB representation for each index.
                                            let mut encoded = Vec::new();
                                            function.encode(&mut encoded);
                                            relocations.push(Relocation {
                                                bytes: offset as usize - range.start as usize
                                                    ..offset as usize - range.start as usize
                                                        + encoded.len(),
                                                function,
                                            });
                                        }
                                    }
                                    ElementItems::Expressions(_, items) => {
                                        for expression in items {
                                            relocations.extend(references(
                                                expression
                                                    .map_err(|error| error.to_string())?
                                                    .get_operators_reader(),
                                                range.start as usize,
                                            )?);
                                        }
                                    }
                                }
                            }
                        }
                        Payload::GlobalSection(section) => {
                            for global in section.clone() {
                                relocations.extend(references(
                                    global
                                        .map_err(|error| error.to_string())?
                                        .init_expr
                                        .get_operators_reader(),
                                    range.start as usize,
                                )?);
                            }
                        }
                        Payload::TableSection(section) => {
                            for table in section.clone() {
                                if let TableInit::Expr(expression) =
                                    table.map_err(|error| error.to_string())?.init
                                {
                                    relocations.extend(references(
                                        expression.get_operators_reader(),
                                        range.start as usize,
                                    )?);
                                }
                            }
                        }
                        _ => {}
                    }
                    let raw = Rc::from(&bytes[range.start as usize..range.end as usize]);
                    module.section(&RawSection {
                        id,
                        data: &relocate(&raw, &relocations, &indices).0,
                    });
                }
            }
        }
    }
    Ok((module.finish(), output_sources))
}
