// harness: compile-fail E0282
//! A closure's parameter type must be known where the parameter is used; a
//! later call does not help. (Checking mode would supply it: see the text.)

// ANCHOR: len
pub fn total_length() -> usize {
    let len = |s| s.len();
    len("checked") + len("synthesized")
}
// ANCHOR_END: len
