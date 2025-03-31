// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use crate::{
    add_code_to_module,
    format::FormatWith,
    module::{Module, Modules},
};
use indoc::indoc;

pub fn add_to_module(to: &mut Module) {
    let code = indoc! { r#"
        fn lt(lhs, rhs) {
            match cmp(lhs, rhs) {
                Less => true,
                _ => false,
            }
        }

        fn le(lhs, rhs) {
            match cmp(lhs, rhs) {
                Greater => false,
                _ => true,
            }
        }

        fn gt(lhs, rhs) {
            match cmp(lhs, rhs) {
                Greater => true,
                _ => false,
            }
        }

        fn ge(lhs, rhs) {
            match cmp(lhs, rhs) {
                Less => false,
                _ => true,
            }
        }

        fn min(lhs, rhs) {
            match cmp(lhs, rhs) {
                Less => lhs,
                _ => rhs,
            }
        }

        fn max(lhs, rhs) {
            match cmp(lhs, rhs) {
                Greater => lhs,
                _ => rhs,
            }
        }

        fn clamp(value, min_bound, max_bound) {
            if gt(min_bound, max_bound) {
                panic("min_bound must be less than or equal to max_bound")
            } else {
                max(min_bound, min(value, max_bound))
            }
        }

        // Arrays

        // Blocked due to issue: https://github.com/enlightware/ferlium/issues/59
        // fn array_peek_back(array) {
        //     let l = array_len(array);
        //     if le(l, 0) {
        //         None
        //     } else {
        //         Some(array[sub(l, 1)])
        //     }
        // }

        // Iterator functions

        /// Returns true if the collection contains no elements.
        fn is_empty(seq) {
            eq(len(seq), 0)
        }

        /*
        // This requires capture to be of realistic use
        fn try_fold(it, init, f) {
            let mut accum = init;
            loop {
                match next(it) {
                    Some(x) => {
                        match f(accum, x) {
                            Continue(v) => {
                                accum = v;
                            },
                            Break => {
                                soft_break
                            }
                        }
                    },
                    None => soft_break,
                }
            };
            accum
        }
        */

        /// Tests if every element of the iterator matches a predicate.
        fn all(it, f) {
            // When capture is available, do:
            // try_fold(it, (), |_accum, x| if f(x) { Continue(()) } else { Break })
            let mut it = it;
            let mut result = true;
            loop {
                match next(it) {
                    Some(x) => {
                        if f(x) {
                            () // not is currently not available in the prelude
                        } else {
                            result = false;
                            soft_break;
                        }
                    },
                    None => soft_break,
                }
            };
            result
        }

        /// Tests if any element of the iterator matches a predicate.
        fn any(it, f) {
            // When capture is available, build on try_fold (see fn all)
            let mut it = it;
            let mut result = false;
            loop {
                match next(it) {
                    Some(x) => {
                        if f(x) {
                            result = true;
                            soft_break;
                        }
                    },
                    None => soft_break,
                }
            };
            result
        }

        // Compatibility, mark as deprecated when supported
        fn array_all(array: [_], f) {
            all(array_iter(array), f)
        }
        fn array_any(array: [_], f) {
            any(array_iter(array), f)
        }

        // Iterator and Seq for ranges
        impl Iterator {
            fn next(a) {
                range_iterator_next(a)
            }
        }
        impl Seq {
            fn iter(a) {
                range_iter(a)
            }
        }
        impl SizedSeq {
            fn len(a) {
                range_len(a)
            }
        }

        // Iterator and Seq for array
        impl Iterator {
            fn next(a) {
                array_iterator_next(a)
            }
        }
        impl Seq {
            fn iter(a) {
                array_iter(a)
            }
        }
        // Requires per trait method generics
        // impl FromIterator {
        //     fn from_iter(it) {
        //         let mut it = it;
        //         let mut a = [];
        //         loop {
        //             match next(it) {
        //                 Some(x) => {
        //                     array_append(a, x);
        //                 },
        //                 None => soft_break,
        //             }
        //         };
        //         a
        //     }
        // }
        impl SizedSeq {
            fn len(a) {
                array_len(a)
            }
        }

        // Serde for basic types
        impl Serialize {
            fn serialize(v: ()) {
                None
            }
        }
        impl Deserialize {
            fn deserialize(v) -> () {
                match (v) {
                    None => (),
                    Seq(a) => {
                        if eq(array_len(a), 0) {
                            ()
                        } else {
                            panic("Expected array of size 0")
                        }
                    },
                    _ => panic("Expected None variant or Seq variant of size 0")
                }
            }
        }
        impl Serialize {
            fn serialize(v: bool) {
                Bool(v)
            }
        }
        impl Deserialize {
            fn deserialize(v) -> bool {
                match (v) {
                    Bool(v) => v,
                    _ => panic("Expected Bool variant")
                }
            }
        }
        impl Serialize {
            fn serialize(v: int) {
                Int(v)
            }
        }
        impl Deserialize {
            fn deserialize(v) -> int {
                match (v) {
                    Int(v) => v,
                    _ => panic("Expected Int variant")
                }
            }
        }
        impl Serialize {
            fn serialize(v: float) {
                Float(v)
            }
        }
        impl Deserialize {
            fn deserialize(v) -> float {
                match (v) {
                    Float(v) => v,
                    Int(v) => from_int(v),
                    _ => panic("Expected Float or Int variant")
                }
            }
        }
        impl Serialize {
            fn serialize(v: string) {
                String(v)
            }
        }
        impl Deserialize {
            fn deserialize(v) -> string {
                match (v) {
                    String(v) => v,
                    _ => panic("Expected String variant")
                }
            }
        }

        // Serde for arrays
        impl Serialize {
            fn serialize(a) {
                let mut result = [];
                for i in range(0, array_len(a)) {
                    array_append(result, serialize(a[i]));
                };
                Seq(result)
            }
        }
        impl Deserialize {
            fn deserialize(a) {
                match (a) {
                    Seq(a) => {
                        let mut result = [];
                        for i in range(0, array_len(a)) {
                            array_append(result, deserialize(a[i]));
                        };
                        result
                    },
                    _ => panic("Expected Seq variant")
                }
            }
        }
    "# };
    add_code_to_module(code, to, &Modules::new()).unwrap_or_else(|e| {
        panic!(
            "Failed to add prelude to module: {}",
            FormatWith::new(&e, &code)
        )
    });
}
