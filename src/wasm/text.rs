// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Wasm text format of a compiled module, with source links for the IDE.

use std::{io, ops::Range};

use wasmparser::{Parser, Payload};
use wasmprinter::{Config, Print};

use crate::{
    CompilerSession, Location,
    emit_mir::{MirText, TextSourceMapEntry},
    eval::RuntimeError,
    module::{FunctionId, LocalFunctionId, ModuleId, id::Id},
};

use super::{
    Imports,
    emit::{self, CodeSourceMapEntry},
};

/// Compile every physical entry of the module into one Wasm module and print it. Functions
/// declared in the source with a scalar signature are exported as `module::function`, as they
/// would be for the Rust host binding.
pub(crate) fn module_text(
    session: &CompilerSession,
    module_id: ModuleId,
) -> Result<MirText, RuntimeError> {
    let program = session.prepare_physical_program(module_id)?;
    let artifacts = program
        .module(module_id)
        .expect("the requested module was assembled");
    let roots = (0..artifacts.entry_count())
        .map(LocalFunctionId::from_index)
        .filter(|&id| artifacts.get(id).is_some())
        .map(|id| FunctionId::new(module_id, id))
        .collect::<Vec<_>>();
    if roots.is_empty() {
        return Ok(MirText {
            text: String::new(),
            source_map: Vec::new(),
        });
    }
    let exports = source_exports(session, module_id, &roots)
        .filter(|(function, _)| emit::host_signature(&program, *function).is_ok())
        .collect::<Vec<_>>();
    let mut imports = Imports::new()
        .map_err(|error| RuntimeError::Backend(format!("Wasm imports: {error:?}")))?;
    let emitted = emit::emit(&program, &roots, &exports, &mut imports, session)
        .map_err(RuntimeError::Backend)?;
    print(&emitted.bytes, &emitted.source_map)
        .map_err(|error| RuntimeError::Backend(format!("Wasm printing: {error}")))
}

/// The roots declared in the module source, with their `module::function` export names.
/// Compiler-generated functions, such as the top-level expression or lambdas, also have names,
/// but these do not appear at their declaration.
fn source_exports<'a>(
    session: &'a CompilerSession,
    module_id: ModuleId,
    roots: &'a [FunctionId],
) -> impl Iterator<Item = (FunctionId, String)> + 'a {
    let module = session.expect_fresh_module(module_id);
    let source = session.get_module_source(module_id);
    let path = session.modules().path(module_id);
    roots.iter().filter_map(move |&function| {
        let (source, path) = (source?, path.as_ref()?);
        let name = module.get_function_name_by_id(function.function)?;
        let declared = module
            .get_function_by_id(function.function)?
            .spans
            .as_ref()?
            .name;
        let declared_name = source.source.get(declared.as_range())?;
        (declared.source_id() == source.source_id
            && (declared_name == name.as_str()
                || declared_name.strip_prefix("r#") == Some(name.as_str())))
        .then(|| (function, format!("{path}::{name}")))
    })
}

/// Print a module, linking each instruction line to the source of the code containing it.
/// Consecutive lines of the same source region form a single link.
fn print(bytes: &[u8], source_map: &[CodeSourceMapEntry]) -> Result<MirText, String> {
    let mut printer = LinePrinter::default();
    Config::new()
        .print(bytes, &mut printer)
        .map_err(|error| error.to_string())?;
    let bodies = code_bodies(bytes)?;
    let text = printer.text;
    let mut links: Vec<TextSourceMapEntry> = Vec::new();
    for (start, offset) in printer.lines {
        let Some(span) = offset.and_then(|offset| span_at(&bodies, source_map, offset as usize))
        else {
            continue;
        };
        let line = &text[start..];
        let line = &line[..line.find('\n').unwrap_or(line.len())];
        let from = start + line.len() - line.trim_start().len();
        let to = start + line.trim_end().len();
        match links.last_mut() {
            Some(last) if last.span == span && text[last.to..from].trim().is_empty() => {
                last.to = to;
            }
            _ => links.push(TextSourceMapEntry { from, to, span }),
        }
    }
    Ok(MirText {
        text,
        source_map: links,
    })
}

/// Module byte ranges of the code-section entries, starting at their local declarations.
fn code_bodies(bytes: &[u8]) -> Result<Vec<Range<usize>>, String> {
    let mut bodies = Vec::new();
    for payload in Parser::new(0).parse_all(bytes) {
        if let Payload::CodeSectionEntry(body) = payload.map_err(|error| error.to_string())? {
            let range = body.range();
            bodies.push(range.start as usize..range.end as usize);
        }
    }
    Ok(bodies)
}

/// The source region of the code at a module byte offset, if any.
fn span_at(
    bodies: &[Range<usize>],
    source_map: &[CodeSourceMapEntry],
    offset: usize,
) -> Option<Location> {
    let body = bodies.partition_point(|range| range.end <= offset);
    let range = bodies.get(body)?;
    let offset = offset.checked_sub(range.start)?;
    // Entries are ordered by body, then by their disjoint byte ranges.
    let index = source_map.partition_point(|entry| (entry.body, entry.bytes.end) <= (body, offset));
    source_map
        .get(index)
        .filter(|entry| entry.body == body && entry.bytes.contains(&offset))
        .map(|entry| entry.span)
}

/// Collects the printed text and the binary offset, if any, at which each line starts.
#[derive(Default)]
struct LinePrinter {
    text: String,
    lines: Vec<(usize, Option<u64>)>,
}

impl Print for LinePrinter {
    fn write_str(&mut self, s: &str) -> io::Result<()> {
        self.text.push_str(s);
        Ok(())
    }

    fn start_line(&mut self, binary_offset: Option<u64>) {
        self.lines.push((self.text.len(), binary_offset));
    }
}

#[cfg(test)]
mod tests {
    use wasm_bindgen_test::wasm_bindgen_test;

    use crate::{CompilerSession, Path};

    use super::module_text;

    const SOURCE: &str = "fn helper(x: int) -> int { x * 3 }\n\
        fn compute(x: int) -> int { if x > 0 { helper(x) } else { 1 } }\n\
        fn pair(x: int) -> (int, int) { (x, helper(x)) }\n\
        fn apply(x: int) -> int { let f = |y| y + 1; f(x) }\n\
        fn r#fn(x: int) -> int { x }\n\
        compute(2)";

    #[wasm_bindgen_test]
    fn module_text_exports_named_functions_and_links_source() {
        let mut session = CompilerSession::new();
        let module = session
            .compile(SOURCE, "wasm_text", Path::single_str("wasm_text"))
            .unwrap()
            .module_id;
        let text = module_text(&session, module).unwrap();
        // Scalar signatures are exported; the tuple result is compiled but not exported.
        assert!(
            text.text.contains("(export \"wasm_text::compute\""),
            "{}",
            text.text
        );
        assert!(text.text.contains("(export \"wasm_text::helper\""));
        assert!(!text.text.contains("(export \"wasm_text::pair\""));
        assert!(text.text.contains("wasm_text::pair"), "{}", text.text);
        assert!(text.text.contains("(export \"wasm_text::apply\""));
        assert!(text.text.contains("(export \"wasm_text::fn\""));
        // Compiler-generated functions are compiled but not exported, even when they have names.
        assert_eq!(text.text.matches("(export ").count(), 5, "{}", text.text);
        assert!(text.text.contains("(export \"setup\""));
        assert!(!text.source_map.is_empty());
        for entry in &text.source_map {
            assert!(entry.from < entry.to && entry.to <= text.text.len());
        }
        // The multiplication links to the call of its native implementation.
        let mul = SOURCE.find("x * 3").unwrap();
        assert!(text.source_map.iter().any(|entry| {
            entry.span.start_usize() == mul
                && entry.span.end_usize() == mul + "x * 3".len()
                && text.text[entry.from..entry.to].contains("call $std::Num<std::int>::mul")
        }));
    }
}
