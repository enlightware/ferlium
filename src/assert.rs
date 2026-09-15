// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use ustr::{Ustr, UstrSet};

pub fn assert_unique_strings<T>(vec: &[(Ustr, T)]) {
    let mut set = UstrSet::default();
    for (s, _) in vec {
        assert!(set.insert(*s), "Duplicate string found: {s}");
    }
}
