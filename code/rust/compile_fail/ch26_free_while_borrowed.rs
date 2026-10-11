// harness: compile-fail E0505
//! The Lean program `uaf` in Rust: a second pointer to a boxed value, the box
//! freed, the pointer used. Rust refuses to free while the borrow is live.

// ANCHOR: uaf
pub fn use_after_free() -> i32 {
    let x = Box::new(42);
    let y = &*x;
    drop(x);
    *y
}
// ANCHOR_END: uaf
