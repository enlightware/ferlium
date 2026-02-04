// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

// cSpell:ignore noplayground

use std::collections::BTreeSet;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process;

use directories::ProjectDirs;
use ferlium::error::CompilationError;
use ferlium::eval::{ControlFlow, RuntimeError};
use ferlium::{CompilerSession, ModuleAndExpr};
use pulldown_cmark::{CodeBlockKind, Event, Options, Parser, Tag, TagEnd};
use sha2::{Digest, Sha256};

#[derive(Debug)]
enum RunError {
    Compilation(CompilationError),
    Runtime(RuntimeError),
}

#[derive(Clone, Copy, Default)]
struct Stats {
    total: usize,
    passed: usize,
    failed: usize,
    ignored: usize,
}

impl Stats {
    fn add(&mut self, other: Stats) {
        self.total += other.total;
        self.passed += other.passed;
        self.failed += other.failed;
        self.ignored += other.ignored;
    }
}

struct CacheEntry {
    content_hash: String,
    stats: Stats,
}

fn main() {
    let mut args = env::args().skip(1);
    let Some(book_arg) = args.next() else {
        eprintln!("Usage: validate_book <path-to-book>");
        process::exit(2);
    };

    let book_root = normalize_book_root(Path::new(&book_arg));
    let src_dir = book_root.join("src");
    if !src_dir.exists() {
        eprintln!("Book src directory does not exist: {}", src_dir.display());
        process::exit(2);
    }

    let mut files = Vec::new();
    if let Err(error) = collect_markdown_files(&src_dir, &mut files) {
        eprintln!("Failed to read book sources: {error}");
        process::exit(2);
    }
    files.sort();

    let mut stats = Stats::default();
    for file in files {
        if let Err(error) = process_markdown_file(&file, &mut stats) {
            eprintln!("Failed to process {}: {error}", file.display());
            stats.failed += 1;
        }
    }

    println!(
        "Summary: {} total, {} passed, {} failed, {} ignored",
        stats.total, stats.passed, stats.failed, stats.ignored
    );

    if stats.failed > 0 {
        process::exit(1);
    }
}

fn normalize_book_root(book_arg: &Path) -> PathBuf {
    if book_arg.file_name().is_some_and(|name| name == "book.toml") {
        book_arg
            .parent()
            .map(Path::to_path_buf)
            .unwrap_or_else(|| book_arg.to_path_buf())
    } else {
        book_arg.to_path_buf()
    }
}

fn collect_markdown_files(dir: &Path, out: &mut Vec<PathBuf>) -> std::io::Result<()> {
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            collect_markdown_files(&path, out)?;
        } else if path.extension().is_some_and(|ext| ext == "md") {
            out.push(path);
        }
    }
    Ok(())
}

fn process_markdown_file(path: &Path, stats: &mut Stats) -> Result<(), String> {
    let content = fs::read_to_string(path)
        .map_err(|error| format!("Failed to read {}: {error}", path.display()))?;

    let content_hash = hash_content(&content);
    if let Some(cached_stats) = load_cached_stats(path, &content_hash) {
        stats.add(cached_stats);
        return Ok(());
    }

    let mut parser = Parser::new_ext(&content, Options::all());
    let mut in_code_block = false;
    let mut code_info = String::new();
    let mut code_body = String::new();
    let mut block_index = 0usize;
    let mut file_stats = Stats::default();

    while let Some(event) = parser.next() {
        match event {
            Event::Start(Tag::CodeBlock(CodeBlockKind::Fenced(info))) => {
                in_code_block = true;
                code_info = info.to_string();
                code_body.clear();
            }
            Event::End(TagEnd::CodeBlock) => {
                if let Some((language, attrs)) = parse_code_info(&code_info) {
                    if language == "ferlium" {
                        block_index += 1;
                        let block_label = format!("{}#block-{}", path.display(), block_index);
                        let result = process_ferlium_block(&block_label, &attrs, &code_body);
                        file_stats.total += 1;
                        match result {
                            BlockResult::Ignored => file_stats.ignored += 1,
                            BlockResult::Passed => file_stats.passed += 1,
                            BlockResult::Failed => file_stats.failed += 1,
                        }
                    }
                }
                in_code_block = false;
            }
            Event::Text(text) if in_code_block => {
                code_body.push_str(&text);
            }
            _ => {}
        }
    }

    stats.add(file_stats);
    store_cached_stats(path, &content_hash, file_stats);

    Ok(())
}

fn load_cached_stats(source_path: &Path, expected_hash: &str) -> Option<Stats> {
    let cache_path = cache_file_path(source_path)?;
    let content = fs::read_to_string(cache_path).ok()?;
    let cache_entry = parse_cache_entry(&content)?;
    if cache_entry.content_hash == expected_hash {
        Some(cache_entry.stats)
    } else {
        None
    }
}

fn store_cached_stats(source_path: &Path, content_hash: &str, stats: Stats) {
    let Some(cache_path) = cache_file_path(source_path) else {
        return;
    };

    if let Some(parent) = cache_path.parent() {
        let _ = fs::create_dir_all(parent);
    }

    let cache_content = format!(
        "v1\nhash={content_hash}\ntotal={}\npassed={}\nfailed={}\nignored={}\n",
        stats.total, stats.passed, stats.failed, stats.ignored
    );
    let _ = fs::write(cache_path, cache_content);
}

fn cache_file_path(source_path: &Path) -> Option<PathBuf> {
    let project_dirs = ProjectDirs::from("dev", "Ferlium", "validate_ferlium_book")?;
    let source_key = source_path.to_string_lossy();
    let source_hash = hash_bytes(source_key.as_bytes());
    Some(
        project_dirs
            .cache_dir()
            .join(format!("{source_hash}.cache")),
    )
}

fn parse_cache_entry(cache_content: &str) -> Option<CacheEntry> {
    let mut lines = cache_content.lines();
    if lines.next()? != "v1" {
        return None;
    }

    let mut hash = None;
    let mut total = None;
    let mut passed = None;
    let mut failed = None;
    let mut ignored = None;

    for line in lines {
        let (key, value) = line.split_once('=')?;
        match key {
            "hash" => hash = Some(value.to_string()),
            "total" => total = value.parse::<usize>().ok(),
            "passed" => passed = value.parse::<usize>().ok(),
            "failed" => failed = value.parse::<usize>().ok(),
            "ignored" => ignored = value.parse::<usize>().ok(),
            _ => return None,
        }
    }

    Some(CacheEntry {
        content_hash: hash?,
        stats: Stats {
            total: total?,
            passed: passed?,
            failed: failed?,
            ignored: ignored?,
        },
    })
}

fn hash_content(content: &str) -> String {
    hash_bytes(content.as_bytes())
}

fn hash_bytes(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    let digest = hasher.finalize();
    format!("{:x}", digest)
}

fn parse_code_info(info: &str) -> Option<(String, Vec<String>)> {
    let mut tokens = info
        .split(|ch: char| ch == ',' || ch.is_whitespace())
        .filter(|token| !token.is_empty());
    let language = tokens.next()?.to_string();
    let attrs = tokens.map(|token| token.to_string()).collect();
    Some((language, attrs))
}

#[derive(Debug)]
enum BlockResult {
    Ignored,
    Passed,
    Failed,
}

fn process_ferlium_block(label: &str, attrs: &[String], code_body: &str) -> BlockResult {
    let allowed_attrs: BTreeSet<&str> = [
        "ignore",
        "no_run",
        "should_panic",
        "compile_fail",
        "editable",
        "noplayground",
    ]
    .into_iter()
    .collect();

    let mut unknown = Vec::new();
    for attr in attrs {
        if !allowed_attrs.contains(attr.as_str()) {
            unknown.push(attr.clone());
        }
    }

    if !unknown.is_empty() {
        println!("[FAIL] {label}: unknown attributes: {}", unknown.join(", "));
        return BlockResult::Failed;
    }

    let ignore = attrs.iter().any(|attr| attr == "ignore");
    if ignore {
        println!("[IGNORED] {label}");
        return BlockResult::Ignored;
    }

    let no_run = attrs.iter().any(|attr| attr == "no_run");
    let should_panic = attrs.iter().any(|attr| attr == "should_panic");
    let compile_fail = attrs.iter().any(|attr| attr == "compile_fail");

    let code = strip_hidden_lines(code_body);

    if compile_fail {
        match compile_only(label, &code) {
            Ok(()) => {
                println!("[FAIL] {label}: expected compile failure but succeeded");
                BlockResult::Failed
            }
            Err(error) => {
                println!("[OK] {label}: compile failed as expected ({error:?})");
                BlockResult::Passed
            }
        }
    } else if no_run {
        match compile_only(label, &code) {
            Ok(()) => {
                println!("[OK] {label}: compiled (no_run)");
                BlockResult::Passed
            }
            Err(error) => {
                println!("[FAIL] {label}: compilation failed ({error:?})");
                BlockResult::Failed
            }
        }
    } else if should_panic {
        match run_block(label, &code, true) {
            BlockResult::Passed => {
                println!("[OK] {label}: panicked as expected");
                BlockResult::Passed
            }
            BlockResult::Failed => {
                println!("[FAIL] {label}: expected panic but ran successfully");
                BlockResult::Failed
            }
            BlockResult::Ignored => BlockResult::Ignored,
        }
    } else {
        match run_block(label, &code, false) {
            BlockResult::Passed => {
                println!("[OK] {label}");
                BlockResult::Passed
            }
            BlockResult::Failed => {
                println!("[FAIL] {label}: runtime or compilation error");
                BlockResult::Failed
            }
            BlockResult::Ignored => BlockResult::Ignored,
        }
    }
}

fn strip_hidden_lines(code: &str) -> String {
    let mut output = String::new();
    for (idx, line) in code.split('\n').enumerate() {
        if idx > 0 {
            output.push('\n');
        }
        if let Some(rest) = line.strip_prefix("# ") {
            output.push_str(rest);
        } else {
            output.push_str(line);
        }
    }
    output
}

fn compile_only(label: &str, code: &str) -> Result<(), RunError> {
    let mut session = CompilerSession::new();
    let modules = session.new_std_modules();
    session
        .compile(label, code, &modules)
        .map(|_| ())
        .map_err(RunError::Compilation)
}

fn run_block(label: &str, code: &str, expect_panic: bool) -> BlockResult {
    let mut session = CompilerSession::new();
    let modules = session.new_std_modules();

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        try_compile_and_run(label, code, &mut session, &modules)
    }));

    match result {
        Ok(Ok(())) => {
            if expect_panic {
                BlockResult::Failed
            } else {
                BlockResult::Passed
            }
        }
        Ok(Err(RunError::Runtime(error))) => {
            println!("[FAIL] {label}: runtime error ({error:?})");
            if expect_panic {
                BlockResult::Passed
            } else {
                BlockResult::Failed
            }
        }
        Err(_) => {
            if expect_panic {
                BlockResult::Passed
            } else {
                BlockResult::Failed
            }
        }
        Ok(Err(RunError::Compilation(error))) => {
            println!("[FAIL] {label}: compilation failed ({error:?})");
            BlockResult::Failed
        }
    }
}

fn try_compile_and_run(
    label: &str,
    code: &str,
    session: &mut CompilerSession,
    modules: &ferlium::module::Modules,
) -> Result<(), RunError> {
    let ModuleAndExpr { module, expr } = session
        .compile(label, code, modules)
        .map_err(RunError::Compilation)?;

    if let Some(expr) = expr {
        expr.expr
            .eval(module)
            .map(ControlFlow::into_value)
            .map_err(RunError::Runtime)?;
    }

    Ok(())
}
