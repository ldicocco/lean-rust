// harness: compile-fail E0106
//! Elision cannot decide which input the result borrows from: the signature
//! must name the region.

// ANCHOR: longer
pub fn longer(a: &str, b: &str) -> &str {
    if a.len() >= b.len() { a } else { b }
}
// ANCHOR_END: longer
