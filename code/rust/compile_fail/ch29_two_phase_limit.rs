// harness: compile-fail E0499
//! A two-phase borrow tolerates reads before its activation, not writes.

// ANCHOR: two_phase_limit
fn rotate_top(stack: &mut Vec<i32>) {
    stack.push(stack.pop().unwrap());
}
// ANCHOR_END: two_phase_limit
