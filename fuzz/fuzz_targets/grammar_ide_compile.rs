#![no_main]
// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use barkus_core::generate::decode;
use barkus_core::ir::grammar::GrammarIr;
use barkus_core::profile::Profile;
use libfuzzer_sys::fuzz_target;
use std::sync::OnceLock;

const FERLIUM_EBNF: &str = include_str!("../grammar/ferlium.ebnf");
const MAX_TAPE_LEN: usize = 16 * 1024;
const MAX_SOURCE_LEN: usize = 32 * 1024;

fn grammar() -> &'static (GrammarIr, Profile) {
    static GRAMMAR: OnceLock<(GrammarIr, Profile)> = OnceLock::new();
    GRAMMAR.get_or_init(|| {
        let profile = Profile::builder()
            .max_depth(16)
            .max_total_nodes(2_000)
            .repetition_bounds(0, 2)
            .build();
        let grammar = barkus_ebnf::compile(FERLIUM_EBNF).expect("Ferlium EBNF should compile");
        (grammar, profile)
    })
}

fuzz_target!(|tape: &[u8]| {
    if tape.len() < 3 || tape.len() > MAX_TAPE_LEN {
        return;
    }

    let (grammar, profile) = grammar();
    let Ok((ast, _)) = decode(grammar, profile, tape) else {
        return;
    };

    let bytes = ast.serialize();
    if bytes.len() > MAX_SOURCE_LEN {
        return;
    }

    let Ok(source) = String::from_utf8(bytes) else {
        return;
    };

    let mut compiler = ferlium::Compiler::new();
    let _ = compiler.compile(&source);
});
