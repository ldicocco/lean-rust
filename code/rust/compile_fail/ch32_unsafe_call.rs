// harness: compile-fail E0133
//! The safe fragment has no rule for calling an `unsafe fn`: the call is
//! accepted only inside an `unsafe` block, where the programmer takes on its
//! precondition.

// ANCHOR: unsafe_call
pub fn sub_unchecked(x: u32, y: u32) -> u32 {
    x.unchecked_sub(y)
}
// ANCHOR_END: unsafe_call
