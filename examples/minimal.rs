use ferlium::{CompilerSession, Path, run_fn_native};

fn main() {
    let mut session = CompilerSession::new();
    let module_id = session
        .compile(
            "fn answer() -> int { 42 }",
            "demo.fer",
            Path::single_str("demo"),
        )
        .unwrap()
        .module_id;

    let result: isize = run_fn_native!(&session, module_id, "answer", [] -> isize).unwrap();
    assert_eq!(result, 42);
}
