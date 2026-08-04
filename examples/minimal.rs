// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
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
