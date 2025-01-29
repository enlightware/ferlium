// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
mod common;

use test_log::test;

use common::run;
use ferlium::value::Value;

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn quicksort() {
    assert_eq!(
        run(r#"fn swap(a, i, j) {
            let temp = a[i];
            a[i] = a[j];
            a[j] = temp
        }

        fn quicksort(a, lo, hi) {
            if lo >= hi || lo < 0 {
                ()
            } else {
                let p = partition(a, lo, hi);
                quicksort(a, lo, p - 1);
                quicksort(a, p + 1, hi)
            }
        }

        fn partition(a, lo, hi) {
            let pivot = a[hi];
            let mut i = lo;

            for j in lo..hi {
                if a[j] < pivot {
                    swap(a, i, j);
                    i = i + 1
                }
            };

            swap(a, i, hi);

            i
        }

        let mut a = [5, 4, 11, 3, 2, 1, 0, 7];
        quicksort(a, 0, array_len(a) - 1);
        a"#),
        int_a![0, 1, 2, 3, 4, 5, 7, 11],
    );
}
