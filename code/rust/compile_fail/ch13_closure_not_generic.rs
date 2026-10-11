// harness: compile-fail E0308
//! A closure is not generalized: it has one parameter type, fixed by its
//! first use, so it cannot be called at a second type.

// ANCHOR: identity
fn use_twice() {
    let identity = |x| x;
    let n = identity(5);
    let s = identity("five");
}
// ANCHOR_END: identity
