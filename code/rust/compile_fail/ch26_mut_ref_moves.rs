// harness: compile-fail E0382
//! `&mut T` is not `Copy`: a mutable reference is an affine value, moved by
//! assignment like a `String`.

// ANCHOR: two_writers
pub fn two_writers(log: &mut String) {
    let first = log;
    let second = log;
    *first = String::from("a");
    *second = String::from("b");
}
// ANCHOR_END: two_writers
