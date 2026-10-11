// harness: compile-fail E0308
//! A function pointer is just a code address: a closure that captures
//! variables has data to carry and cannot become one.

// ANCHOR: shift
pub fn shift_all(xs: &mut [u32], offset: u32) {
    let shift: fn(u32) -> u32 = |x| x + offset;
    for x in xs {
        *x = shift(*x);
    }
}
// ANCHOR_END: shift
