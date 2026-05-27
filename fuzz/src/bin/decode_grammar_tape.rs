use barkus_core::generate::decode;
use barkus_core::profile::Profile;
use std::env;
use std::fs;
use std::process::ExitCode;

const FERLIUM_EBNF: &str = include_str!("../../grammar/ferlium.ebnf");

fn main() -> ExitCode {
    let mut args = env::args().skip(1);
    let Some(path) = args.next() else {
        eprintln!("usage: decode_grammar_tape <artifact>");
        return ExitCode::FAILURE;
    };

    let tape = match fs::read(&path) {
        Ok(tape) => tape,
        Err(error) => {
            eprintln!("failed to read {path}: {error}");
            return ExitCode::FAILURE;
        }
    };

    let profile = Profile::builder()
        .max_depth(16)
        .max_total_nodes(2_000)
        .repetition_bounds(0, 2)
        .build();
    let grammar = match barkus_ebnf::compile(FERLIUM_EBNF) {
        Ok(grammar) => grammar,
        Err(error) => {
            eprintln!("failed to compile grammar: {error}");
            return ExitCode::FAILURE;
        }
    };

    let (ast, _) = match decode(&grammar, &profile, &tape) {
        Ok(decoded) => decoded,
        Err(error) => {
            eprintln!("failed to decode {path}: {error}");
            return ExitCode::FAILURE;
        }
    };

    match String::from_utf8(ast.serialize()) {
        Ok(source) => {
            print!("{source}");
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("decoded source is not UTF-8: {error}");
            ExitCode::FAILURE
        }
    }
}
