use std::collections::HashSet;

pub fn assert_unique_strings<T>(vec: &Vec<(String, T)>) {
    let mut set = HashSet::new();
    for (s, _) in vec {
        assert!(set.insert(s), "Duplicate string found: {}", s);
    }
}
