// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{
    fmt::Write,
    fs,
    path::{Path, PathBuf},
    process::Command,
};

use sha2::{Digest, Sha256};

fn files_below(root: &Path, extension: &str) -> Vec<PathBuf> {
    fn visit(path: &Path, extension: &str, files: &mut Vec<PathBuf>) {
        let mut entries = fs::read_dir(path)
            .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()))
            .map(|entry| entry.expect("failed to read directory entry").path())
            .collect::<Vec<_>>();
        entries.sort();
        for entry in entries {
            if entry.is_dir() {
                visit(&entry, extension, files);
            } else if entry.extension().is_some_and(|value| value == extension) {
                files.push(entry);
            }
        }
    }

    let mut files = Vec::new();
    visit(root, extension, &mut files);
    files
}

fn fingerprint(
    files: impl IntoIterator<Item = PathBuf>,
    context: impl IntoIterator<Item = (String, String)>,
) -> String {
    let mut files = files.into_iter().collect::<Vec<_>>();
    files.sort();
    let mut hash = Sha256::new();
    for path in files {
        println!("cargo::rerun-if-changed={}", path.display());
        let path_bytes = path.to_string_lossy();
        let contents = fs::read(&path)
            .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()));
        hash.update((path_bytes.len() as u64).to_le_bytes());
        hash.update(path_bytes.as_bytes());
        hash.update((contents.len() as u64).to_le_bytes());
        hash.update(contents);
    }
    let mut context = context.into_iter().collect::<Vec<_>>();
    context.sort();
    for (name, value) in context {
        hash.update((name.len() as u64).to_le_bytes());
        hash.update(name.as_bytes());
        hash.update((value.len() as u64).to_le_bytes());
        hash.update(value.as_bytes());
    }
    let digest = hash.finalize();
    let mut fingerprint = String::with_capacity(digest.len() * 2);
    for byte in digest {
        write!(fingerprint, "{byte:02x}").expect("writing to a String cannot fail");
    }
    fingerprint
}

fn main() {
    let std_source_fingerprint = fingerprint(files_below(Path::new("src/std"), "fer"), []);
    println!("cargo::rustc-env=FERLIUM_STD_SOURCE_FINGERPRINT={std_source_fingerprint}");

    // Hash compiler inputs conservatively. The snapshot is compiler-owned internal data: an
    // unrelated edit may invalidate it unnecessarily, but source, macro, dependency, target, and
    // feature changes cannot accidentally share an incompatible cache entry.
    let mut semantic_files = files_below(Path::new("src"), "rs");
    semantic_files.extend(files_below(Path::new("src"), "lalrpop"));
    semantic_files.extend(files_below(Path::new("ferlium_macros/src"), "rs"));
    semantic_files.extend([
        PathBuf::from("Cargo.toml"),
        PathBuf::from("Cargo.lock"),
        PathBuf::from("build.rs"),
        PathBuf::from("ferlium_macros/Cargo.toml"),
    ]);
    let mut build_context = std::env::vars()
        .filter(|(name, _)| {
            name.starts_with("CARGO_CFG_")
                || name.starts_with("CARGO_FEATURE_")
                || matches!(
                    name.as_str(),
                    "TARGET" | "HOST" | "PROFILE" | "OPT_LEVEL" | "DEBUG"
                )
        })
        .collect::<Vec<_>>();
    if let Some(rustc) = std::env::var_os("RUSTC") {
        let version = Command::new(&rustc)
            .arg("-vV")
            .output()
            .ok()
            .filter(|output| output.status.success())
            .map(|output| String::from_utf8_lossy(&output.stdout).into_owned())
            .unwrap_or_else(|| rustc.to_string_lossy().into_owned());
        build_context.push(("RUSTC_VERSION".to_owned(), version));
    }
    let semantic_fingerprint = fingerprint(semantic_files, build_context);
    println!("cargo::rustc-env=FERLIUM_SEMANTIC_BUILD_FINGERPRINT={semantic_fingerprint}");

    lalrpop::process_src().unwrap();
}
