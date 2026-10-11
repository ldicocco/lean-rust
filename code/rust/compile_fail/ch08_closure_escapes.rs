// harness: compile-fail E0373
//! Without `move`, a closure captures `n` by reference; returning it would
//! leave a reference to a local variable that no longer exists.

// ANCHOR: make_adder
pub fn make_adder(n: u32) -> impl Fn(u32) -> u32 {
    |x| x + n
}
// ANCHOR_END: make_adder
