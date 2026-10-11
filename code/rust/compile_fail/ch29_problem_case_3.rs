// harness: compile-fail E0499
//! NLL problem case #3: a borrow returned on one path of a `match` is
//! considered live on the other path too.

use std::collections::HashMap;

// ANCHOR: problem_case_3
fn get_default<'r>(cache: &'r mut HashMap<u32, String>, key: u32) -> &'r mut String {
    match cache.get_mut(&key) {
        Some(value) => value,
        None => {
            cache.insert(key, String::new());
            cache.get_mut(&key).unwrap()
        }
    }
}
// ANCHOR_END: problem_case_3
