// harness: compile-fail E0121
//! Signatures are boundaries: no inference across them, not even when the
//! compiler knows the answer.

// ANCHOR: double
fn double(x: i32) -> _ {
    x * 2
}
// ANCHOR_END: double
