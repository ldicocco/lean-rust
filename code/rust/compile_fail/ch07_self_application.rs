// harness: compile-fail E0282
//! Self-application `λx. x x` as a Rust closure: to call `x`, its type must be
//! known, and no type can describe it.

// ANCHOR: delta
pub fn delta() {
    let self_apply = |x| x(x);
}
// ANCHOR_END: delta
