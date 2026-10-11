// harness: compile-fail E0502
//! Derivation II in real Rust: a shared borrow of `v` is still in use when
//! `v.push` needs a mutable one.

// ANCHOR: aliasing_bug
pub fn aliasing_bug() {
    let mut v: Vec<i32> = vec![1, 2, 3];
    let first: &i32 = &v[0];
    v.push(4);
    println!("{first}");
}
// ANCHOR_END: aliasing_bug
