use ustr::{Ustr, UstrSet};

pub fn assert_unique_strings<T>(vec: &[(Ustr, T)]) {
    let mut set = UstrSet::default();
    for (s, _) in vec {
        assert!(set.insert(*s), "Duplicate string found: {}", s);
    }
}
