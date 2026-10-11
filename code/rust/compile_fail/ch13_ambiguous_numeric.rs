// harness: compile-fail E0689
//! A method call needs the receiver's type now; integer defaulting happens
//! only at the end of the function, which is too late.

// ANCHOR: square
fn area() -> u64 {
    let side = 12;
    let squared = side.pow(2);
    squared
}
// ANCHOR_END: square
