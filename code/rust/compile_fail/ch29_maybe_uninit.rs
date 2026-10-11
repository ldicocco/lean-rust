// harness: compile-fail E0381
//! The move analysis follows paths, not values: `warm` might be false.

// ANCHOR: maybe_uninit
fn calibrate(warm: bool) -> i32 {
    let offset: i32;
    if warm {
        offset = 2;
    }
    offset
}
// ANCHOR_END: maybe_uninit
